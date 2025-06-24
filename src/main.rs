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

            // Wait until a key is requested AND the key slot is empty.
            // Precondition for `GenerateKey`: `\E i: image_states[i] = "PendingKey" /\ keys = "Empty"`
            state = cvar.wait_while(state, |s| {
                (s.image_states.iter().all(|&st| st != ImageState::PendingKey) || s.keys != KeyState::Empty)
                && s.keys_used < N
            }).unwrap();

            // If all keys have been set, no more keys will be requested.
            if state.keys_used == N {
                break;
            }

            // As per `GenerateKey`, this thread only modifies `keys`.
            println!("KeyGen: Generating key...");
            state.keys = KeyState::Generated;
            println!("KeyGen: Key is 'Generated'.");

            cvar.notify_all(); // Notify workers that the key is ready.
        }
    });
    handles.push(key_gen_handle);

    // --- Image Loader Threads ---
    for thread_id in 0..2 {
        let pair_clone = Arc::clone(&pair);
        let handle = thread::spawn(move || {
            loop {
                let (lock, cvar) = &*pair_clone;
                let mut state = lock.lock().unwrap();

                // Check if all images are loaded.
                if state.image_states.iter().all(|&s| s == ImageState::Loaded) {
                    break;
                }

                // --- Try to perform an action ---

                // Action: SetKey(i)
                // Pre: keys = "Generated" AND image_states[i] = "PendingKey"
                if state.keys == KeyState::Generated {
                    if let Some(idx) = state.image_states.iter().position(|s| *s == ImageState::PendingKey) {
                        state.keys = KeyState::Empty;
                        state.image_states[idx] = ImageState::HasKey;
                        state.keys_used += 1;
                        println!("Thread {}: SetKey for image {} (total keys used: {})", thread_id, Image(idx).0, state.keys_used);
                        cvar.notify_all();
                        continue; // Restart loop to release lock and re-evaluate state
                    }
                }

                // Action: FinishLoad(i)
                // Pre: image_states[i] = "HasKey"
                if let Some(idx) = state.image_states.iter().position(|s| *s == ImageState::HasKey) {
                    state.image_states[idx] = ImageState::Loaded;
                    println!("Thread {}: FinishLoad for image {}", thread_id, Image(idx).0);
                    cvar.notify_all();
                    continue;
                }

                // Action: StartLoad(i)
                // Pre: image_states[i] = "None" AND no other image is "PendingKey"
                let is_any_pending = state.image_states.iter().any(|s| *s == ImageState::PendingKey);
                if !is_any_pending {
                    if let Some(idx) = state.image_states.iter().position(|s| *s == ImageState::None) {
                        state.image_states[idx] = ImageState::PendingKey;
                        println!("Thread {}: StartLoad for image {}", thread_id, Image(idx).0);
                        cvar.notify_all();
                        continue;
                    }
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
        // Wait until all images are fully loaded.
        while state.image_states.iter().any(|&s| s != ImageState::Loaded) {
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
