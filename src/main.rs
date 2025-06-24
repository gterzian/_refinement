use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// From TLA+ spec: CONSTANT N
const N: usize = 10;

// From TLA+ spec: ImageState == {"None", "Loaded"}
// The "Loading" state has been removed to more closely match the TLA+ spec,
// which models the load operation as a single atomic action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    Loaded,
}

// The TLA+ spec defines `Image == 1..N`. We represent an image's ID using the
// newtype pattern as requested.
#[derive(Debug, Clone, Copy)]
struct Image(usize);

// The shared state protected by the Mutex.
// From TLA+ spec: VARIABLES image_states, keys_used
struct SharedState {
    // `image_states` is a direct translation of the TLA+ map `[Image -> ImageState]`,
    // where the vector index corresponds to the image ID.
    image_states: Vec<ImageState>,
    keys_used: usize, // This will count fully loaded images
}

fn main() {
    // From TLA+ spec: Init == /\ image_states = [i \in Image |-> "None"]
    //                         /\ keys_used = 0
    let pair = Arc::new((
        Mutex::new(SharedState {
            image_states: vec![ImageState::None; N],
            keys_used: 0,
        }),
        Condvar::new(),
    ));

    let mut handles = vec![];

    // Run two threads as requested.
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

                    // Perform the "work". In a real system, this would be I/O.
                    // Here, we simulate it with a sleep.
                    // This is happening *inside* the lock, which is a direct translation
                    // of the atomic action in the TLA+ spec, but is not a good pattern
                    // for real-world concurrent code as it blocks other threads.
                    thread::sleep(Duration::from_millis(250));

                    // This corresponds to the state change in the TLA+ action `LoadImage(i)`
                    state.image_states[idx] = ImageState::Loaded;
                    state.keys_used += 1;
                    println!(
                        "Thread {}: Finished loading image {} (total loaded: {})",
                        thread_id, Image(idx).0, state.keys_used
                    );

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
