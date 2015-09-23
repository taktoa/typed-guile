<!-- --- mode: markdown; coding: utf-8 --- -->

# Roadmap

## Phase 1 – Implementation in Haskell

- [ ] Write a type checker for Guile in Haskell.
  - [ ] Fix [Tandoori][] such that it can successfully typecheck Haskell.
  - [ ] Write a program that normalizes the syntax of Guile to be easily parsed
        by a Haskell parser.
    - [x] Run Guile reader on input.
    - [x] Annotate syntax information to include line numbers concretely.
    - [ ] Annotate syntax with available type information
          (i.e.: add types to literals).
    - [ ] Do scope analysis and create an AST populated exclusively with
          fully-qualified (vis-à-vis modules) unique identifiers
    - [ ] Write normalizers for various built-in types using GOOPS `class-of`
      - [ ] [Booleans][guile-bool]:
        - `#t –> (@class@ <boolean> #t)`
        - `#f –> (@class@ <boolean> #f)`
      - [ ] [Numbers][guile-num]:
        - [ ] `534 –> (@class@ <integer> 534)`
        - [ ] `5/6 –> (@class@ <fraction> 5/6)`
        - [ ] `5.3 –> (@class@ <real> 5.3)`
      - [ ] [Characters][guile-char]:
        - `#\b –> (@class@ <char> #\b)`
      - [ ] [Strings][guile-str]:
        - `"hello" –> (@class@ <string> "hello")`
      - [ ] [Symbols][guile-sym]:
        - `'hello –> (@class@ <symbol> 'hello)`
      - [ ] [Keywords][guile-kw]:
        - `#:example –> (@class@ <keyword> #:example)`
      - [ ] [Arrays][guile-vec]:
        - `#(1 2 3) –> (@class@ <vector> #(1 2 3))`
      - [ ] [Arrays][guile-arr]:
        - `#@2(1 2 3) –> (@class@ <array> #@2(1 2 3))`
      - [ ] [Bytevectors][guile-bv]:
        - `#vu8(1 53 204) –> (@class@ <bytevector> 1 53 204)`
      - [ ] [Bitvectors][guile-bits]:
        - `#*10101 –> (@class@ <bitvector> #b10101)`
      - [ ] Docstrings: run the `texinfo` parser on all docstrings.
    - [ ] Write test cases for the normalizer using SRFI-64.
  - [ ] Write a Haskell module that launches Guile to normalize an input string.
  - [ ] Make a parser in Haskell for s-expressions (should return a rose tree).
    - Use `attoparsec` or `parsec` for parsing.
  - [ ] Make a GADT representing the annotated Guile AST.
  - [ ] Write a function that takes the rose tree and outputs the typed tree.
  - [ ] Abstract out the GHC API from Tandoori.
  - [ ] Wire together the Tandoori code and the typed Guile AST.
  - [ ] Successfully type basic arithmetic expressions in Guile.

## Phase 2 – Type System Work

  - [ ] Write typing judgments and test cases for a lot of code.
  - Benchmarks:
    - [ ] Typecheck code involving:
      - [ ] Monomorphic types
        - [ ] Booleans
        - [ ] Numbers
        - [ ] Characters
        - [ ] Strings
        - [ ] Bitvectors
        - [ ] Bytevectors
        - [ ] Quasiquoting
        - [ ] `*unspecified*`
      - [ ] Polymorphic types
        - [ ] Lists
          - [ ] Homogeneous lists
          - [ ] Heterogeneous lists
        - [ ] Vectors
        - [ ] Arrays
        - [ ] Hash tables
      - [ ] Complex types
        - [ ] Modules
        - [ ] Objects
      - [ ] Type signatures
        - [ ] Prefix syntax
        - [ ] Infix syntax
        - [ ] Top-level
        - [ ] Inline
        - [ ] Scoped type variables
      - [ ] Algebraic data types
        - [ ] Enumerated types
        - [ ] Polymorphic ADTs
        - [ ] GADTs
      - [ ] Typeclasses
        - [ ] Class definitions
        - [ ] Instances
        - [ ] Multi-parameter type classes
        - [ ] Flexible instances
        - [ ] Functional dependencies
        - [ ] Maintainable type classes
      - [ ] Control flow
        - [ ] Conditional
          - [ ] `if`
          - [ ] `cond`
          - [ ] `when`/`unless`
          - [ ] `case`
          - [ ] `match`
        - [ ] Iteration
          - [ ] `do`
          - [ ] `while`
          - [ ] Named `let`
      - [ ] Nonlinear program flow
        - [ ] Continuations
          - [ ] Prompts
            - [ ] `call-with-prompt`
            - [ ] `make-prompt-tag`
            - [ ] `default-prompt-tag`
            - [ ] `abort-to-prompt`
          - [ ] Escape
            - [ ] `call-with-escape-continuation`
            - [ ] `let-escape-continuation`
          - [ ] Delimited
            - [ ] `shift`/`reset`
          - [ ] Unrestricted
            - [ ] `call-with-current-continuation`
            - [ ] `dynamic-wind`
        - [ ] Exceptions
        - [ ] Signals
        - [ ] Parameters
        - [ ] Continuation barriers
    - [ ] Functions
        - [ ] Single-argument
        - [ ] Nullary
        - [ ] Multiple arguments
        - [ ] Rest arguments
        - [ ] Keyword arguments
      - [ ] Binding
        - [ ] Local
          - [ ] `let`
          - [ ] `let*`
          - [ ] `letrec`
          - [ ] `letrec*`
        - [ ] Global
          - [ ] `define` for values
          - [ ] `define` for functions
          - [ ] `define*`
      - [ ] Macros
        - [ ] `define-syntax-rule`
        - [ ] Hygienic macros
        - [ ] Procedural macros
    - [ ] Typecheck Guile compiler.
      - [x] Typecheck 0%   of the Guile compiler.
      - [ ] Typecheck 20%  of the Guile compiler.
      - [ ] Typecheck 40%  of the Guile compiler.
      - [ ] Typecheck 60%  of the Guile compiler.
      - [ ] Typecheck 80%  of the Guile compiler.
      - [ ] Typecheck 100% of the Guile compiler.
    - [ ] Typecheck all Guile SRFIs.
      - [ ] SRFI-0:   `cond-expand`
      - [ ] SRFI-1:   List library
      - [ ] SRFI-2:   `and-let*`
      - [ ] SRFI-4:   Homogeneous numeric vector datatypes
      - [ ] SRFI-6:   Basic string ports
      - [ ] SRFI-8:   `receive`
      - [ ] SRFI-9:   `define-record-type`
      - [ ] SRFI-10:  Hash-comma reader extension
      - [ ] SRFI-11:  `let-values`
      - [ ] SRFI-13:  String library
      - [ ] SRFI-14:  Character-set library
      - [ ] SRFI-16:  `case-lambda`
      - [ ] SRFI-17:  Generalized `set!`
      - [ ] SRFI-18:  Multithreading support
      - [ ] SRFI-19:  Time/Date library
      - [ ] SRFI-23:  Error reporting
      - [ ] SRFI-26:  Specializing parameters
      - [ ] SRFI-27:  Sources of random bits
      - [ ] SRFI-30:  Nested multi-line comments
      - [ ] SRFI-31:  Recursive evaluation
      - [ ] SRFI-34:  Exception handling for programs
      - [ ] SRFI-35:  Conditions
      - [ ] SRFI-37:  `args-fold`
      - [ ] SRFI-38:  Abstract binding syntax
      - [ ] SRFI-39:  Parameters
      - [ ] SRFI-41:  Streams
      - [ ] SRFI-42:  Eager comprehensions
      - [ ] SRFI-43:  Vector library
      - [ ] SRFI-45:  Iterative lazy algorithm primitives
      - [ ] SRFI-46:  Basic `syntax-rules` extensions
      - [ ] SRFI-55:  Requiring features
      - [ ] SRFI-60:  Integers as bits
      - [ ] SRFI-61:  A more general `cond` clause
      - [ ] SRFI-62:  Comments in s-expressions
      - [ ] SRFI-64:  Test suites
      - [ ] SRFI-67:  Comparison procedures
      - [ ] SRFI-69:  Basic hash tables
      - [ ] SRFI-87:  `=>` in `case` clauses
      - [ ] SRFI-88:  Keywords
      - [ ] SRFI-98:  Accessing environment variables
      - [ ] SRFI-105: Curly-infix expressions
      - [ ] SRFI-111: Boxes

## Phase 3 – Porting to Typed Guile

- [ ] Port the type checker to Typed Guile.

## Phase 4 – Guile Compiler Integration

- [ ] Integrate the Guile typechecker into the Guile compiler.
- [ ] Port the Guile compiler to Typed Guile.
- Typed Guile should be self-hosting at this point.

## Phase 5 – Tooling

- [ ] Make an exhaustiveness checker for pattern matching.
  - [GADTs meet their match][]
- [ ] Implement refinement types.
  - [LiquidHaskell][liquidhaskell]
  - [Z3 Prover][z3-prover]
  - [Rosette][rosette]
- [ ] Make a totality checker.
  - [Catch: Case Totality Checker for Haskell][catch-totality]
- [ ] Make a numerical stability linter.
  - [Herbie][herbie]
  - [Herbie GHC Plugin][herbie-ghc]
- [ ] Work on `guildhall`, the Guile package manager.
  - [ ] Make the `guildhall` website (https://guildhall.io)
- [ ] Fix [guile-lint][].
- [ ] Make profile-guided typing tool.

# Design Decisions

## Parsing

- We should use [derivative parsers][derp] in general (though we will probably
  wait until we have ported, i.e.: after phase 2).

## Type system

### Continuations

- Luckily, `call-with-current-continuation` is quite rare in Guile.
  - It is only used a few times in the Guile compiler.
- Delimited continuations (as defined in `(ice-9 control)`) are, however, used
  quite a few times.
- Perhaps we could type these with the [Cont monad][cont-monad].

### Typeclasses

- Relevant papers:
  - [Maintainable Type Classes for Haskell][maintain-tc]

### Effects

- Should we go with monadic IO or uniqueness typing?
- For layering of effects, should we use monad transformers, algebraic effects,
  or extensible effects?
- What are the tradeoffs here vis-à-vis usability, learnability, expressiveness,
  type system complexity?
- Relevant papers:
  - [Algebraic Effects in Idris][idris-alg]
  - [Uniqueness Types in Idris][idris-uniq]
  - [RWH: Monad Transformers][rwh-monad-transformers]
  - [Extensible Effects: An Alternative to Monad Transformers][exteff]
  - [Freer Monads, More Extensible Effects][more-exteff]
  - [The effects package in Hackage][hackage-effects]

## Typing Guile semantics

### Functions

- Should functions be curried in the type system, despite not being curried in 
  the operational semantics of Scheme?
- Keyword/Rest Arguments
  - We should type keyword and rest arguments by translating to HM types.
  - There are a variety of ways to type keywords and rest arguments, most of
    which are listed [here][polyvariadic].

### Objects

- I think we can mostly type GOOPS classes as being open type classes.
  - Basically, any time a class is declared, create a type class, and then add
    a method to that type class for every unique generic method that takes a
    thing with that type.
  - Whenever you encounter polymorphism (i.e.: two generic methods with the same
    name and different types), encode that as an instance of the typeclass.
  - It may actually be worth it to expose open type classes as a user-accessible
    feature outside of type system hackery.

## Other decisions

### Modules

- Should we bother typing modules?
- The [1ML system][] is rather promising for typing modules.
- [Backpack][] is also interesting and worth looking at.

### Tooling

- We should fix [guile-lint][]
- We should make a usable terminal UI for Guile, à la [Elm][elm-errors].
  - It would be neat to make it even fancier with a powerline-style top bar.
  - Writing a library for ANSI colors etc. in Guile would be useful.
  - Porting [boxes][], [vty-ui][], or [brick][] could also be useful.
- Profile-guided after-the-fact typing would be very useful for translating the
  Guile compiler (and other untyped Guile libraries) to Typed Guile.
  - [Profile-Guided Static Typing for Dynamic Scripting Languages][prof-type]
- We should have automatic tools for translating [Haskell][], [Typed Racket][], 
  [Typed Clojure][], [SML][], and [OCaml][] to Typed Guile (or, at the very 
  least, have tools for importing type signatures).
- A Guile project generator, à la `cabal init`, would be very nice.
  - It should generate all of the following files:
    - FIXME 

[Tandoori]:
  http://gergo.erdi.hu/projects/tandoori/
[1ML system]:
  http://www.mpi-sws.org/~rossberg/1ml/
[guile-lint]:
  http://user42.tuxfamily.org/guile-lint/
[elm-errors]:
  http://elm-lang.org/blog/compiler-errors-for-humans
[maintain-tc]:
  http://ff32.host.cs.st-andrews.ac.uk/papers/hsym15.pdf
[idris-uniq]:
  http://idris.readthedocs.org/en/latest/reference/uniqueness-types.html
[idris-alg]:
  http://eb.host.cs.st-andrews.ac.uk/drafts/effects.pdf
[polyvariadic]:
  http://okmij.org/ftp/Haskell/polyvariadic.html
[boxes]:
  http://hackage.haskell.org/package/boxes
[vty-ui]:
  http://hackage.haskell.org/package/vty-ui
[brick]:
  http://hackage.haskell.org/package/brick
[exteff]:
  http://okmij.org/ftp/Haskell/extensible/exteff.pdf
[more-exteff]:
  http://okmij.org/ftp/Haskell/extensible/more.pdf
[rwh-monad-transformers]:
  http://book.realworldhaskell.org/read/monad-transformers.html#id6594
[Haskell]:
  http://haskell.org
[Typed Racket]:
  http://docs.racket-lang.org/ts-guide/index.html
[Typed Clojure]:
  http://github.com/clojure/core.typed
[SML]:
  http://sml-family.org
[OCaml]:
  http://caml.inria.fr/pub/docs/manual-ocaml/
[derp]:
  http://hackage.haskell.org/package/derp
[prof-type]:
  http://www.cs.umd.edu/projects/PL/druby/papers/druby-tr-4935.pdf
[cont-monad]:
  http://hackage.haskell.org/package/mtl/docs/Control-Monad-Cont.html
[hackage-effects]:
  http://hackage.haskell.org/package/effects
[guile-bool]:
  http://www.gnu.org/software/guile/manual/html_node/Booleans.html
[guile-num]:
  http://www.gnu.org/software/guile/manual/html_node/Numbers.html
[guile-char]:
  http://www.gnu.org/software/guile/manual/html_node/Characters.html
[guile-str]:
  http://www.gnu.org/software/guile/manual/html_node/Strings.html
[guile-sym]:
  http://www.gnu.org/software/guile/manual/html_node/Symbols.html
[guile-kw]:
  http://www.gnu.org/software/guile/manual/html_node/Keywords.html
[guile-vec]:
  http://www.gnu.org/software/guile/manual/html_node/Vectors.html
[guile-arr]:
  http://www.gnu.org/software/guile/manual/html_node/Arrays.html
[guile-bv]:
  http://www.gnu.org/software/guile/manual/html_node/Bytevectors.html
[guile-bits]:
  http://www.gnu.org/software/guile/manual/html_node/Bit-Vectors.html
[catch-totality]:
  http://community.haskell.org/~ndm/catch/
[liquid-haskell]:
  http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about
[herbie]:
  http://herbie.uwplse.org
[herbie-ghc]:
  https://github.com/mikeizbicki/HerbiePlugin
[GADTs meet their match]:
  http://research.microsoft.com/en-us/um/people/simonpj/papers/pattern-matching/gadtpm.pdf
[z3-prover]:
  https://github.com/Z3Prover/z3
[rosette]:
  http://homes.cs.washington.edu/~emina/rosette/guide/index.html
[Backpack]:
  http://plv.mpi-sws.org/backpack
