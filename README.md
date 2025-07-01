### Accompanying material for [`A Tale of Two Refinements`](https://medium.com/@polyglot_factotum/a-tale-of-two-refinements-f6cdb2a3e4d8)

#### Steps used to get `main.rs` in [this state](https://github.com/gterzian/_refinement/blob/68666036d233045e885907f299d45c30ab10093e/src/main.rs):

The steps used to get to [this state](https://github.com/gterzian/_refinement/blob/68666036d233045e885907f299d45c30ab10093e/src/main.rs) are described [here](steps.md).

#### Further changes made after review of the code
- Further review of the code showed that only one key would be generated at a time, which led to the [following interaction](code_review.md), resulting in this [final iteration of the code](/src/main.rs). 

#### Full chat history

The full chat history is available [here](chat_history.md).

#### Notes about the commit history:

- Up to [`remove .DS_Store`](https://github.com/gterzian/_refinement/commit/af8eb1eda5f2a4f3868edfd5718254452b7a6c6a)
  I was messing around, and I also accidentally switched models used.
- So I started again, by deleting the contents of `main.rs`, adding `prompt.md`, and by sticking to Gemini 2.5 Pro.
- The story in the blog post starts with [`with prompt, first, gemini`](https://github.com/gterzian/_refinement/commit/4874109e8dcdba9605f35283ce85c497629bfa5a), arrives at a pre-review state of [`seventh, and final, take. It's a wrap.`](https://github.com/gterzian/_refinement/commit/68666036d233045e885907f299d45c30ab10093e), and then arrives at a final state by way of a more careful review of the code(detailed above).
- There are a few more commits consisting of clean-ups to make the material more presentable(example: the prompt contained typos).
