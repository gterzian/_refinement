use std::collections::{HashMap, VecDeque};
use std::env;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

// CONSTANT N
// Note: N is provided as a command-line argument.

/// Image == 1..N
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
struct Image(usize);

/// ImageState == {"None", "PendingKey", "HasKey", "Loaded"}
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
enum ImageState {
    #[default]
    None,
    PendingKey,
    HasKey,
    Loaded,
}

// Note: Represents a "Generated" key from the spec.
#[derive(Debug)]
struct Key;

/// TypeOk == /\ image_states \in [Image -> ImageState]
///           /\ image_queue \in Seq(Image)
///           /\ keys_used \in Int
///           /\ keys \in Seq({"Generated"})
///           /\ pending_keys \in [Thread -> BOOLEAN]
struct SharedState {
    /// image_states \in [Image -> ImageState]
    image_states: HashMap<Image, ImageState>,
    /// image_queue \in Seq(Image)
    image_queue: VecDeque<Image>,
    /// keys_used \in Int
    keys_used: u32,
    /// keys \in Seq({"Generated"})
    keys: VecDeque<Key>,
    // Note: This single boolean represents the state of `pending_keys`.
    // `false` means `\A t \in Thread: pending_keys[t] = FALSE`.
    // `true` means `\E t \in Thread: pending_keys[t] = TRUE`.
    // This is necessary because threads are anonymous in this implementation.
    /// pending_keys \in [Thread -> BOOLEAN]
    pending_keys: bool,
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: cargo run -- <N> <NUM_THREADS>");
        std::process::exit(1);
    }

    let n: usize = args[1].parse().expect("N must be a positive integer");
    let num_threads: usize = args[2]
        .parse()
        .expect("NUM_THREADS must be a positive integer");

    // Image == 1..N
    let images: Vec<Image> = (1..=n).map(Image).collect();
    // Note: The spec defines `Thread == 1..N`, which would tie the number of threads to the
    // number of images `N`. The prompt requires the number of threads to be configurable
    // independently. The implementation of `pending_keys` with a single boolean accommodates
    // this requirement by abstracting away thread identities.

    // Init
    let initial_state = {
        // /\ image_states = [i \in Image |-> "None"]
        let image_states = images.iter().map(|&i| (i, ImageState::default())).collect();
        // /\ image_queue = <<>>
        let image_queue = VecDeque::new();
        // /\ keys_used = 0
        let keys_used = 0;
        // /\ keys = <<>>
        let keys = VecDeque::new();
        // /\ pending_keys = [t \in Thread |-> FALSE]
        let pending_keys = false;

        SharedState {
            image_states,
            image_queue,
            keys_used,
            keys,
            pending_keys,
        }
    };

    let lock = Arc::new(Mutex::new(initial_state));
    let cvar = Arc::new(Condvar::new());
    let mut handles = vec![];

    for _ in 0..num_threads {
        let lock_clone = Arc::clone(&lock);
        let cvar_clone = Arc::clone(&cvar);
        let images_clone = images.clone();

        let handle = thread::spawn(move || {
            let mut guard = lock_clone.lock().unwrap();
            // BatchingSpec  ==  Init  /\  [][Next]_<<...>>
            loop {
                // Done
                // /\ \A ii \in Image: image_states[ii] = "Loaded"
                if guard
                    .image_states
                    .values()
                    .all(|&s| s == ImageState::Loaded)
                    && guard.image_queue.is_empty()
                {
                    // Note: The system stops when the Done action is the only one possible.
                    // This requires the image_queue to be empty, otherwise DequeImage would
                    // still be enabled.
                    cvar_clone.notify_all();
                    break;
                }

                // Next == \/ \E i \in Image: \/ StartLoad(i)
                //                           \/ FinishLoad(i)
                //                           \/ DequeImage(i)
                //                           \/ SetKey(i)
                //         \/ Done
                //         \/ \E t \in Thread:
                //             \/ StartKeyGeneration(t)
                //             \/ GenerateKeys(t)
                let mut action_taken = false;

                // StartKeyGeneration(t)
                // /\ \A tt \in Thread: pending_keys[tt] = FALSE
                if !guard.pending_keys {
                    // LET keys_requested == Cardinality({i \in Image: image_states[i] = "PendingKey"})
                    let keys_requested = guard
                        .image_states
                        .values()
                        .filter(|&&s| s == ImageState::PendingKey)
                        .count();
                    // LET keys_needed == keys_requested - Len(keys)
                    let keys_needed = keys_requested.saturating_sub(guard.keys.len());
                    // /\ pending_keys' = [pending_keys EXCEPT ![t] = keys_needed > 0]
                    if keys_needed > 0 {
                        guard.pending_keys = true;
                        action_taken = true;
                    }
                }

                if !action_taken {
                    // GenerateKeys(t)
                    // /\ pending_keys[t] = TRUE
                    if guard.pending_keys {
                        // LET keys_requested == Cardinality({i \in Image: image_states[i] = "PendingKey"})
                        let keys_requested = guard
                            .image_states
                            .values()
                            .filter(|&&s| s == ImageState::PendingKey)
                            .count();
                        // LET keys_needed == keys_requested - Len(keys)
                        let keys_needed = keys_requested.saturating_sub(guard.keys.len());
                        // LET batch == [i \in 1..keys_needed |-> "Generated"]
                        let batch: VecDeque<Key> = (0..keys_needed).map(|_| Key).collect();
                        // /\ keys' = keys \o batch
                        guard.keys.extend(batch);
                        // /\ pending_keys' = [pending_keys EXCEPT ![t] = FALSE]
                        guard.pending_keys = false;
                        action_taken = true;
                    }
                }

                if !action_taken {
                    if let Some(&image_at_head) = guard.image_queue.front() {
                        let state_at_head = *guard.image_states.get(&image_at_head).unwrap();

                        match state_at_head {
                            ImageState::PendingKey => {
                                // SetKey(i)
                                // /\ Head(image_queue) = i
                                // /\ image_states[i] = "PendingKey"
                                // /\ Len(keys) > 0
                                if !guard.keys.is_empty() {
                                    // /\ keys' = Tail(keys)
                                    guard.keys.pop_front();
                                    // /\ keys_used' = keys_used + 1
                                    guard.keys_used += 1;
                                    // /\ image_states' = [image_states EXCEPT ![i] = "HasKey"]
                                    guard.image_states.insert(image_at_head, ImageState::HasKey);
                                    action_taken = true;
                                }
                            }
                            ImageState::HasKey => {
                                // FinishLoad(i)
                                // /\ Head(image_queue) = i
                                // /\ image_states[i] = "HasKey"
                                // /\ image_states' = [image_states EXCEPT ![i] = "Loaded"]
                                guard.image_states.insert(image_at_head, ImageState::Loaded);
                                action_taken = true;
                            }
                            ImageState::Loaded => {
                                // DequeImage(i)
                                // /\ Len(image_queue) > 0
                                // /\ Head(image_queue) = i
                                // /\ image_states[i] = "Loaded"
                                // /\ image_queue' = Tail(image_queue)
                                guard.image_queue.pop_front();
                                // /\ keys' = <<>>
                                guard.keys.clear();
                                action_taken = true;
                            }
                            ImageState::None => {}
                        }
                    }
                }

                if !action_taken {
                    // \E i \in Image
                    for &image in images_clone.iter() {
                        // StartLoad(i)
                        // /\ image_states[i] = "None"
                        if *guard.image_states.get(&image).unwrap() == ImageState::None {
                            // /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                            guard.image_states.insert(image, ImageState::PendingKey);
                            // /\ image_queue' = Append(image_queue, i)
                            guard.image_queue.push_back(image);
                            action_taken = true;
                            // Note: A thread performs only one action per iteration before waiting.
                            break;
                        }
                    }
                }

                if action_taken {
                    cvar_clone.notify_all();
                }

                guard = cvar_clone.wait(guard).unwrap();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Program ran successfully and now stops.");

    let final_state = lock.lock().unwrap();
    assert_eq!(
        final_state.keys_used, n as u32,
        "Final keys_used should be N"
    );
    assert!(
        final_state
            .image_states
            .values()
            .all(|&s| s == ImageState::Loaded),
        "All images should be in the 'Loaded' state"
    );
    assert!(
        final_state.image_queue.is_empty(),
        "Final image_queue should be empty"
    );
    assert!(final_state.keys.is_empty(), "Final keys should be empty");
    assert!(
        !final_state.pending_keys,
        "Final pending_keys should be false"
    );
}
