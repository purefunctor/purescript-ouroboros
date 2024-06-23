# purescript-ouroboros

Ouroboros is a PureScript compiler written in PureScript, with its name derived from an ancient symbol depicting a serpent or dragon eating its own tail [^1].

PureScript is a small, strongly-typed programming language with expressive types that compiles to JavaScript (and other languages!), inspired by and originally written in Haskell.

## Design

Ouroboros aims to provide a modernized compiler implementation with a strong focus on performance and reactivity that is on par with other languages such TypeScript, or even OCaml and Rust. Declarative programming appears as a core theme in Ouroboros' architecture. 

Rather than large compiler phases which imperatively accumulate information, it consists of small functions which derive information. For instance, rather than mutating an environment when type-checking with local bindings, Ouroboros uses a [scope graph](https://pl.ewi.tudelft.nl/research/projects/scope-graphs/) to model name resolution rules in the language.

Consequently, its declarative design makes way for incremental recomputation. Ouroboros' party of small functions is designed to compute information that is tolerant to changes that won't affect semantics. For example, adding a comment should not cause the entire file to be type-checked, though it might be useful to recomptue information such as source spans for hover tooltips in the editor.

The [DESIGN.md](./DESIGN.md) document talks these design choices and inspirations in-depth.

## Performance

Ouroboros currently compiles to JavaScript, which would entail reservations about its performance. To maximize performance, the implementation embraces mutable state and uncurried functions in hot code paths. This combination allows code with little overhead to be generated for crucial functions such as AST traversals. Otherwise, non-critical code is implemented in a more "idiomatic" style.

In the future, Ouroboros aims to be compiled with the Chez Scheme backend, [purescm](https://github.com/purescm/purescm), which offers significantly improved performance over JavaScript runtimes.

## Compatibility

Ouroboros aims to achieve parity with _the_ current PureScript compiler release, with the goal of being able to compile compatible packages in the [PureScript Registry](https://github.com/purescript/registry). On the other hand, Ouroboros does not have this guarantee for the unhappy path—compiler errors may be improved, revamped, or even removed entirely. Likewise, there are no guarantees about code generation. For now, the primary compilation target of Ouroboros is the `CoreFn` representation, which is consumed by code generation backends.

[^1]: https://en.wikipedia.org/wiki/Ouroboros
