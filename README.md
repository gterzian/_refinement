Accompanying material for [`A Tale of Two Refinements`](https://medium.com/@polyglot_factotum/a-tale-of-two-refinements-f6cdb2a3e4d8)


Note about the commit history:

- Up to [`remove .DS_Store`](https://github.com/gterzian/_refinement/commit/af8eb1eda5f2a4f3868edfd5718254452b7a6c6a)
  I was messing around, and I also accidentally switched models used.
- So I started again, by deleting the contents of `main.rs`, adding `prompt.md`, and by sticking to Gemini 2.5 Pro.
- The story in the blog post starts with [`with prompt, first, gemini`](https://github.com/gterzian/_refinement/commit/4874109e8dcdba9605f35283ce85c497629bfa5a), and ends with [`seventh, and final, take. It's a wrap.`](https://github.com/gterzian/_refinement/commit/68666036d233045e885907f299d45c30ab10093e)
- The last few commits are manual edits after all the code generation to fix some typos(mine) and naming issues(mine again, in the spec names) to make the material more presentable.

Steps used to get `main.rs` in [this state](https://github.com/gterzian/_refinement/blob/68666036d233045e885907f299d45c30ab10093e/src/main.rs):

1.  Using Github Copilot chat, with Gemini 2.5 Pro as model.
2.  Deleted contents of `main.rs`(see note on commit history above), deleted chat history, and attached `ImageCacheOne.tla` and `prompt.md` to the context.
3.  Prompted: "Do". This resulted in [this iteration of the code](https://github.com/gterzian/_refinement/commit/4874109e8dcdba9605f35283ce85c497629bfa5a).
4.  Attached `ImageCacheTwo.tla` to context, and prompted:
    > Now, using `ImageCacheTwo.tla` as a design document, write a second iteration of the system according to the same guidelines in `prompt.md`.
    This resulted in [this iteration of the code](https://github.com/gterzian/_refinement/commit/967a57bb7d5738df9b9acd9bb1fc208055dd74ce).
5.  Attached `ImageCacheThree.tla` to context, and prompted:
    > Now, using `ImageCacheThree.tla`, but ignoring `keys_batch`, as a design document, write another iteration of the system according to the same guidelines in prompt.md.
    This resulted in [this iteration of the code](https://github.com/gterzian/_refinement/commit/de75ed47337ef1ed1fe269938da86b39eec8fefd).
6.  Updated [`prompt.md`](https://github.com/gterzian/_refinement/commit/0ad3527f2e6f007720dd6e5c86c4af8fb10b672e) and prompted:
    > The `action_taken` variable creates a livelock, because the program will keep alternating on `guard.pending_keys`.
    >
    > I have updated `prompt.md` to allow for more than one action taken per thread iteration, which should allow you to fix the livelock.
    The edited prompt and resulting code is in [this commit](https://github.com/gterzian/_refinement/commit/0ad3527f2e6f007720dd6e5c86c4af8fb10b672e).
7.  Prompted:
    > The current implementation does not follow the spec, in that the implemention stops when the equivalent of the`Done` action is enabled, but in the prompt I wrote that the system should stop when it is in a state corresponding to infinite stuttering steps of a action such as `Done`, but the implementation stops when there are still images in the queue, which means we are not in an infinite stuttering step state, because `DequeImage` is still enabled.
    >
    > Please fix it.
    This came with an edit to the prompt (to emphasize "infinite") and resulted in a new iteration of the code, [here](https://github.com/gterzian/_refinement/commit/7303a6e7326be5059aeac0d789ced46066c28d53).
8.  Updated the spec to [this state](https://github.com/gterzian/_refinement/commit/c7b02014ec3d18fdd8f8ff14dd0019001cdbbccb), and prompted:
    > I have updated the spec to only generate a batch if needed; please update the code.
    This resulted in this iteration of the code [here](https://github.com/gterzian/_refinement/commit/c7b02014ec3d18fdd8f8ff14dd0019001cdbbccb).
9.  Prompted:
    > I believe the spec allows the batch of keys to be generated outside of the critical section, because this only requires the `keys_needed` variable, which is computed from the shared state as part of `StartKeyGeneration`, after which the program can exit the critical section, generate the batch, and then re-enter the critical section to perform the post conditions of `GenerateKeys`. This does require performing `GenerateKeys` by the same thread who set `pending_keys` to true.
    >
    > If you agree that the spec allows for this, please make the change. If you disagree, do not make changes but explain your reasoning to me.
    This resulted in [this answer](https://gist.github.com/gterzian/611274c52017c7e20e9649e8088219ae).
10. Updated [`prompt.md`](https://github.com/gterzian/_refinement/blob/8889e43192bef5e70b3d0d6f35fc55af3c2b8b22/prompt.md), and prompted:
    > I agree, but, I also believe that main reason for not making the change is not the constraints of the spec, but the constraints of the prompt which forbid assigning identies to threads. So I have now updated the prompt, and I ask you to look at the spec again in that light, and make the changes I proposed above(including changes adding a concept of thread identity if needed) if you now think that is allowed; if not, explain to me why.
    This resulted in [this answer](https://gist.github.com/gterzian/0e1eb20a20a9a6e452683a4fea84ea63).
11. Updated [the spec](https://github.com/gterzian/_refinement/commit/8889e43192bef5e70b3d0d6f35fc55af3c2b8b22#diff-82972e806b99062c2fc570e87ea9663e6e5fa6d36369c199040dcb021c82527a), and prompted:
    > Thank you for pointing this out. I have now updated the spec; please re-consider.
    This resulted in [this iteration of the code](https://github.com/gterzian/_refinement/commit/8889e43192bef5e70b3d0d6f35fc55af3c2b8b22#diff-82972e806b99062c2fc570e87ea9663e6e5fa6d36369c199040dcb021c82527a), and [this answer](https://gist.github.com/gterzian/414ba8a3e88401e2f438214b0180ffae).
12. Prompted:
    > Thank you, couple of things to adress:
    >
    > - Please continue to ignore `keys_batch`, so remove it from the code.
    > - For clarity and consistency, use the newstruct pattern for the thread id as well.
    This resulted in
