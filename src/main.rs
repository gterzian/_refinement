use std::collections::HashMap;
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

/// keys \in {"Empty", "Generated"}
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
enum Keys {
    #[default]
    Empty,
    Generated,
}

/// TypeOk == /\ image_states \in [Image -> ImageState]
///           /\ keys_used \in Int
///           /\ keys \in {"Empty", "Generated"}
struct SharedState {
    /// image_states \in [Image -> ImageState]
    image_states: HashMap<Image, ImageState>,
    /// keys_used \in Int
    keys_used: u32,
    /// keys \in {"Empty", "Generated"}
    keys: Keys,
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

    // Init
    let initial_state = {
        // /\ image_states = [i \in Image |-> "None"]
        let image_states = images.iter().map(|&i| (i, ImageState::default())).collect();
        // /\ keys_used = 0
        let keys_used = 0;
        // /\ keys = "Empty"
        let keys = Keys::default();

        SharedState {
            image_states,
            keys_used,
            keys,
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
            // NonBlockingSpec  ==  Init  /\  [][Next]_<<image_states, keys_used, keys>>
            loop {
                // Done
                // /\ \A ii \in Image: image_states[ii] = "Loaded"
                if guard
                    .image_states
                    .values()
                    .all(|&s| s == ImageState::Loaded)
                {
                    // Note: The system stops when the Done action is the only one possible.
                    cvar_clone.notify_all();
                    break;
                }

                // Next == \/ \E i \in Image: \/ StartLoad(i)
                //                            \/ SetKey(i)
                //                            \/ FinishLoad(i)
                //         \/ Done
                //         \/ GenerateKey
                let mut action_taken = false;

                // GenerateKey
                // /\ \E i \in Image: image_states[i] = "PendingKey"
                if guard
                    .image_states
                    .values()
                    .any(|&s| s == ImageState::PendingKey)
                {
                    // /\ keys = "Empty"
                    if guard.keys == Keys::Empty {
                        // /\ keys' = "Generated"
                        guard.keys = Keys::Generated;
                        action_taken = true;
                    }
                }

                if !action_taken {
                    // \E i \in Image
                    for &image in images_clone.iter() {
                        let current_state = *guard.image_states.get(&image).unwrap();

                        match current_state {
                            ImageState::None => {
                                // StartLoad(i)
                                // /\ image_states[i] = "None"
                                // /\ \A ii \in Image: image_states[ii] # "PendingKey"
                                if !guard
                                    .image_states
                                    .values()
                                    .any(|&s| s == ImageState::PendingKey)
                                {
                                    // /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                                    guard.image_states.insert(image, ImageState::PendingKey);
                                    action_taken = true;
                                }
                            }
                            ImageState::PendingKey => {
                                // SetKey(i)
                                // /\ image_states[i] = "PendingKey"
                                // /\ keys = "Generated"
                                if guard.keys == Keys::Generated {
                                    // /\ keys' = "Empty"
                                    guard.keys = Keys::Empty;
                                    // /\ keys_used' = keys_used + 1
                                    guard.keys_used += 1;
                                    // /\ image_states' = [image_states EXCEPT ![i] = "HasKey"]
                                    guard.image_states.insert(image, ImageState::HasKey);
                                    action_taken = true;
                                }
                            }
                            ImageState::HasKey => {
                                // FinishLoad(i)
                                // /\ image_states[i] = "HasKey"
                                // /\ image_states' = [image_states EXCEPT ![i] = "Loaded"]
                                guard.image_states.insert(image, ImageState::Loaded);
                                action_taken = true;
                            }
                            ImageState::Loaded => {}
                        }

                        if action_taken {
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
    // Note: When all images are loaded, the last action on `keys` must have been
    // `SetKey`, which sets it to `Empty`. No other action can change it after that.
    assert_eq!(final_state.keys, Keys::Empty, "Final keys should be Empty");
}
