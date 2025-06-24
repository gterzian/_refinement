use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// From TLA+ spec: CONSTANT N
const N: usize = 10;

// From TLA+ spec: ImageState == {"None", "PendingKey", "HasKey", "Loaded"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    PendingKey,
    HasKey,
    Loaded,
}

// From TLA+ spec: keys \in {"Empty", "Generated"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeyState {
    Empty,
    Generated,
}

// The TLA+ spec defines `Image == 1..N`.
#[derive(Debug, Clone, Copy)]
struct Image(usize);

// From TLA+ spec: VARIABLES image_states, keys_used, keys
struct SharedState {
    image_states: Vec<ImageState>,
    keys_used: usize,
    keys: KeyState,
}

fn main() {
    // From TLA+ spec: Init
    let pair = Arc::new((
        Mutex::new(SharedState {
            image_states: vec![ImageState::None; N],
            keys_used: 0,
            keys: KeyState::Empty,
        }),
        Condvar::new(),
    ));

    let mut handles = vec![];

    // --- Key Generator Thread ---
    // This thread is responsible for the `GenerateKey` action.
    let key_gen_pair = Arc::clone(&pair);
    let key_gen_handle = thread::spawn(move || {
        loop {
            let (lock, cvar) = &*key_gen_pair;
            let mut state = lock.lock().unwrap();

            // Wait until there is a request for a key (i.e., an image is in `PendingKey` state).
            while state.image_states.iter().all(|&s| s != ImageState::PendingKey) {
                state = cvar.wait(state).unwrap();
            }

            // --- Start of critical section ---
            // Find the first image that is pending a key.
            if let Some(idx) = state.image_states.iter().position(|&s| s == ImageState::PendingKey) {
                println!("KeyGen: Generating key for image {}", Image(idx).0);

                // Simulate key generation time.
                thread::sleep(Duration::from_millis(150));

                // Update the state to reflect that the key has been generated.
                state.image_states[idx] = ImageState::HasKey;
                state.keys_used += 1;
                println!(
                    "KeyGen: Finished generating key for image {} (total keys used: {})",
                    Image(idx).0, state.keys_used
                );

                // Notify the main thread that a key has been generated.
                cvar.notify_all();
            }
            // --- End of critical section (lock is released) ---
        }
    });
    handles.push(key_gen_handle);

    // --- Image Loader Threads ---
    for thread_id in 0..2 {
        let pair_clone = Arc::clone(&pair);
        let handle = thread::spawn(move || {
            loop {
                let (lock, cvar) = &*pair_clone;

                // --- Start of critical section ---
                // The TLA+ `LoadImage` action is atomic. To model this directly,
                // the entire process of finding, "loading", and updating state
                // happens within a single lock.
                let mut state = lock.lock().unwrap();

                // Find an image that is not yet loaded.
                // This corresponds to the TLA+ action precondition: `image_states[i] = "None"`
                let work_item_index = state.image_states.iter().position(|&s| s == ImageState::None);

                if let Some(idx) = work_item_index {
                    println!("Thread {}: Found image to load {}", thread_id, Image(idx).0);

                    // This corresponds to the state change in the TLA+ action `LoadImage(i)`
                    state.image_states[idx] = ImageState::PendingKey;
                    println!("Thread {}: Image {} is pending key", thread_id, Image(idx).0);

                    // From TLA+ spec: Done == /\ \A ii \in Image: image_states[ii] = "Loaded"
                    // We check if our work is done and notify any waiting threads.
                    if state.keys_used == N {
                        println!("Thread {}: All images loaded. Notifying main thread.", thread_id);
                        cvar.notify_all();
                        break; // Exit the loop, this thread's work is done.
                    }
                } else {
                    // No work to claim, so all work is done.
                    // This thread can exit.
                    break;
                }
                // --- End of critical section (lock is released) ---
            }
        });
        handles.push(handle);
    }

    // Main thread waits until the `Done` condition is met.
    // This block ensures the lock is released before joining the threads.
    {
        let (lock, cvar) = &*pair;
        let mut state = lock.lock().unwrap();
        while state.keys_used < N {
            // The condvar atomically unlocks the mutex and waits for a worker to signal.
            state = cvar.wait(state).unwrap();
        }
    } // The lock (`state` guard) is released here.

    println!("\nMain thread: All images have been loaded. Joining worker threads.");

    // Join on the threads to ensure they have completed before exiting.
    for handle in handles {
        handle.join().unwrap();
    }

    println!("\nFinal state:");
    // Re-acquire lock to print the final state.
    let (lock, _) = &*pair;
    let state = lock.lock().unwrap();
    println!("  Keys used: {}", state.keys_used);
    println!("System stopped.");
}
