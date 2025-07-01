Using the TLA+ spec attached to the context as a design document, 
please implement a multithreaded system in `main.rs` with the following features:

- It should run a configurable number of threads that all are able to perform all spec actions--that means not naming threads or assigning roles to them, unless that is implied by the spec. The `N` in the spec should be configurable separatly from the number of threads(please document how to use the program, with example, in your response in the chat).
- The threads should share a struct, protected by a mutex, and associated with a condvar.
- The shared struct should contain the data translated from the TLA+ variables ino their equivalent to idiomatic Rust.
- For sets used in the spec as the domain of functions, translate those into Rust not with a set but with a vector of structs implementing the newtype pattern(where the sole field of the struct corresponds to the type of the set).
- For sets used as the codomain of functions, use an enum, derive `Default`, and mark the right variant as default(based on the `Init` action) using `#[default]`. 
- Functions translate to `HashMap`, where the key is the newtype struct representing the domain, and the value is the enum representing the codomain.
- If the system is meant to end with infinite stuttering steps(for example: infinite stuttering of a `Done` action), the Rust implementation should stop at that point. Please join on the threads when stopping.
- After joining the threads, print "Program ran successfully and now stops." to the console. Then, add assertions about the final state of the program that seem to make sense in order to check that the program implemented the spec.
- When adding comments: 
  - only copy paste from the spec to a Rust comment, do not add additional comments(exceptions below). 
  - Use granular comments, for example: document a block of Rust code(be it an actual block, a function, a method, or just a few lines of code) implementing that action with only the name of the action, and then document each line implementing one or several pre- and post-condition of the action with the corresponding line from the spec. If the Rust code does not map to the spec line to line, explain why in a comment starting with `// Note: `. 
  - Do not mention the reason for, or the source of, the comment(avoid things like: "as per the spec", "following the prompt", or "the prompt requires").
  - Do not comment the equivalent of the `UNCHANGED` conditions.  
- Document data structures and their members with `///`, and use `//` for inline comments.
- Simpler is better: each iteration of the thread should perform only one action(exceptions will be formulated in follow-up prompts if needed), and each iteration should end with a wait on the condvar, unless the system is stopping. If following these constraints would produce a livelock not modeled in the spec(this should be documented), then ignore them, but document this in the code.
- Do not add variables not found in the spec, unless absolutely necessary to translate it into idiomatic Rust(this you can explain in a comment, in an exception to the ban on additional comments stated above). 
  - As an example: if the `Done` state of the spec can be computed from existing variables, a `done` variable or field to a struct is redundant and should be avoided. 
- Do not add explanations to what you are doing in your chat response. The code should speak for itself. 
- Do not add changes, optimizations, or refinements that haven't been asked for: the goal is to follow the spec to the letter, even if this results in a suboptimal system(deadlock, poor performance). The spec may have been written to model such a suboptimal system as an example.
- Ensure your code compiles. 
- Close delimiters.
- Only use the standard library.


#### Further changes made after review of the code
- Further review of the code showed that only one key would be generated at a time, which led to the [following interaction](https://gist.github.com/gterzian/79a3c9ee6f306a067583bcbf00e9354c), resulting in this [final iteration of the code](https://github.com/gterzian/_refinement/blob/9d70e8ca8087ac38b66bfa598de5272151656fef/src/main.rs). 


#### Full chat history

The full chat history is available [here](https://gist.github.com/gterzian/6ae651b9a2cd86a3e3e9b42b66a78305).