#### Further changes made as part of a code review.

gterzian: The current implementation seems to only process one image at a time, while the spec allows more than one image to be in the key, with the goal of generating keys in batches of more than one(on occasion). 

If you agree that the spec allows for this, please change the logic accordingly. 

GitHub Copilot: You are correct. The current implementation only ever puts one image into the `PendingKey` state at a time because the `StartLoad` action is only performed for a single image before the thread waits. This prevents the system from ever requesting a batch of more than one key, which defeats the purpose of the batching logic in the specification.

I have updated the code to allow a thread to perform multiple `StartLoad` actions in a single turn. This will allow multiple images to enter the `PendingKey` state, enabling the system to generate key batches as intended by the spec.

````rust
// ...existing code...
                    if !action_taken {
                        // \E i \in Image
                        // Note: To allow for batching, a thread can perform multiple StartLoad
                        // actions in one turn. This allows multiple images to be in the
                        // PendingKey state, so that key generation can happen in batches.
                        for &image in images_clone.iter() {
                            // StartLoad(i)
                            // /\ image_states[i] = "None"
                            if *guard.image_states.get(&image).unwrap() == ImageState::None {
                                // /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                                guard.image_states.insert(image, ImageState::PendingKey);
                                // /\ image_queue' = Append(image_queue, i)
                                guard.image_queue.push_back(image);
                                action_taken = true;
                            }
                        }
                    }
                }

                if action_taken {
// ...existing code...
````

gterzian: This means all images will always be loaded at the same time, I would rather see some non-determinism. How about removing the conditiona that no action have been taken, and just always perform `StartLoad(i)` if enabled(and breaking if it ran). 

Again only do this if the spec allows it. 

GitHub Copilot: You are correct. The current implementation imposes a strict order on actions that reduces non-determinism. A thread will only attempt to perform a `StartLoad` action if no other actions are available.

The TLA+ specification, however, defines the `Next` step as a disjunction (`\/`) of all possible actions. This means that at any given point, any enabled action can be chosen non-deterministically. The spec allows for a `StartLoad` action to be taken even if other actions like `SetKey` or `FinishLoad` are also enabled.

To better reflect this non-determinism, I will modify the logic. I will remove the `if !action_taken` guard and the `else` block that currently prevents `StartLoad` from being considered when other actions are taken. Instead, the loop will now attempt to perform a `StartLoad` action on the first available image it finds, and if successful, it will set `action_taken` and break from that specific loop, allowing other actions to still be considered within the same thread turn. This change increases the non-determinism of the system while still adhering to the specification.

````rust
// ...existing code...
                    // /\ pending_keys' = [pending_keys EXCEPT ![t] = 0]
                    guard.pending_keys.remove(&id);
                }

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
                            action_taken = true;
                        }
                        ImageState::None => {}
                    }
                }

                // \E i \in Image
                // Note: To increase non-determinism, we check for StartLoad regardless of
                // whether other actions have been taken. This is allowed by the spec,
                // as Next is a disjunction of all actions.
                for &image in images_clone.iter() {
                    // StartLoad(i)
                    // /\ image_states[i] = "None"
                    if *guard.image_states.get(&image).unwrap() == ImageState::None {
                        // /\ image_states' = [image_states EXCEPT ![i] = "PendingKey"]
                        guard.image_states.insert(image, ImageState::PendingKey);
                        // /\ image_queue' = Append(image_queue, i)
                        guard.image_queue.push_back(image);
                        action_taken = true;
                        // Note: Break after one to increase non-determinism.
                        break;
                    }
                }

                if action_taken {
                    cvar_clone.notify_all();
                }
// ...existing code...
````