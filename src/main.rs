use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// From TLA+ spec: CONSTANT N
const N: usize = 10;
const NUM_THREADS: usize = 2;

// From TLA+ spec: ImageState == {"None", "PendingKey", "HasKey", "Loaded"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    PendingKey,
    HasKey,
    Loaded,
}

// The TLA+ spec defines `Image == 1..N`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Image(usize);

// From TLA+ spec: VARIABLES image_states, image_queue, keys_used, keys, pending_keys
struct SharedState {
    image_states: Vec<ImageState>,
    image_queue: VecDeque<Image>,
    keys_used: usize,
    keys: VecDeque<()>, // Represents a sequence of "Generated" keys
    pending_keys: Vec<bool>,
}

fn main() {
    // From TLA+ spec: Init
    let pair = Arc::new((
        Mutex::new(SharedState {
            image_states: vec![ImageState::None; N],
            image_queue: VecDeque::new(),
            keys_used: 0,
            keys: VecDeque::new(),
            pending_keys: vec![false; NUM_THREADS],
        }),
        Condvar::new(),
    ));

    let mut handles = vec![];

    for thread_id in 0..NUM_THREADS {
        let pair_clone = Arc::clone(&pair);
        let handle = thread::spawn(move || {
            loop {
                let (lock, cvar) = &*pair_clone;
                let mut state = lock.lock().unwrap();

                // Done condition
                if state.image_states.iter().all(|&s| s == ImageState::Loaded)
                    && state.image_queue.is_empty()
                {
                    break;
                }

                // --- Try to perform any enabled action ---

                // Action: DequeImage(i)
                if let Some(&image) = state.image_queue.front() {
                    if state.image_states[image.0] == ImageState::Loaded {
                        let dequeued_image = state.image_queue.pop_front().unwrap();
                        // The line `keys' = <<>>` is commented out in the spec, so keys are unchanged.
                        println!("Thread {}: Dequeued image {}", thread_id, dequeued_image.0);
                        cvar.notify_all();
                        continue;
                    }
                }

                // Action: FinishLoad(i)
                if let Some(&image) = state.image_queue.front() {
                    if state.image_states[image.0] == ImageState::HasKey {
                        state.image_states[image.0] = ImageState::Loaded;
                        println!("Thread {}: Finished load for image {}", thread_id, image.0);
                        cvar.notify_all();
                        continue;
                    }
                }

                // Action: SetKey(i)
                if !state.keys.is_empty() {
                    if let Some(&image) = state.image_queue.front() {
                        if state.image_states[image.0] == ImageState::PendingKey {
                            state.keys.pop_front();
                            state.image_states[image.0] = ImageState::HasKey;
                            state.keys_used += 1;
                            println!("Thread {}: Set key for image {}", thread_id, image.0);
                            cvar.notify_all();
                            continue;
                        }
                    }
                }

                // Action: StartKeyGeneration(t) and GenerateKeys(t) are combined.
                let keys_requested = state
                    .image_states
                    .iter()
                    .filter(|&&s| s == ImageState::PendingKey)
                    .count();
                let keys_to_generate = keys_requested.saturating_sub(state.keys.len());
                let no_one_generating = state.pending_keys.iter().all(|&p| !p);
                if keys_to_generate > 0 && no_one_generating {
                    // Claim the right to generate keys
                    state.pending_keys[thread_id] = true;
                    println!(
                        "Thread {}: Starting generation for {} key(s)...",
                        thread_id, keys_to_generate
                    );

                    // Release the lock to perform work outside the critical section
                    drop(state);
                    // The amount of work is proportional to the number of keys needed.
                    thread::sleep(Duration::from_millis(250 * keys_to_generate as u64));

                    // Re-acquire the lock to commit the work
                    let mut state = lock.lock().unwrap();

                    // Now perform the GenerateKeys action logic using the pre-calculated amount.
                    for _ in 0..keys_to_generate {
                        state.keys.push_back(());
                    }
                    println!(
                        "Thread {}: Finished generating {} key(s).",
                        thread_id, keys_to_generate
                    );

                    // Unset the flag, allowing another thread to generate if needed
                    state.pending_keys[thread_id] = false;
                    cvar.notify_all();
                    continue;
                }

                // Action: StartLoad(i)
                if let Some(idx) = state
                    .image_states
                    .iter()
                    .position(|&s| s == ImageState::None)
                {
                    state.image_states[idx] = ImageState::PendingKey;
                    state.image_queue.push_back(Image(idx));
                    println!("Thread {}: Started load for image {}", thread_id, idx);
                    cvar.notify_all();
                    continue;
                }

                // If no action could be taken, wait for a state change.
                state = cvar.wait(state).unwrap();
            }
        });
        handles.push(handle);
    }

    // Main thread waits until the `Done` condition is met.
    {
        let (lock, cvar) = &*pair;
        let mut state = lock.lock().unwrap();
        while state.image_states.iter().any(|&s| s != ImageState::Loaded) {
            state = cvar.wait(state).unwrap();
        }
    }

    println!("\nMain thread: All images have been loaded. Joining worker threads.");
    for handle in handles {
        handle.join().unwrap();
    }

    println!("\nFinal state:");
    let (lock, _) = &*pair;
    let state = lock.lock().unwrap();
    assert!(state.keys.is_empty(), "Keys should be empty at the end.");
    assert!(
        state.image_queue.is_empty(),
        "Image queue should be empty at the end."
    );
    println!("  Keys used: {}", state.keys_used);
    println!("  Image queue length: {}", state.image_queue.len());
    println!("System stopped.");
}
