# -*- mode: org; coding: utf-8 -*-

* Roadmap

** Phase 1 – Implementation in Haskell

```
(set-option :produce-unsat-cores true)
(declare-const a Int)
(declare-const b Int)
(assert (! (> a 10) :named greater))
(assert (! (< a 10) :named lesser))
(assert (! (= b 5) :named lol))
(check-sat)
(get-info :all-statistics)
(get-unsat-core)
```

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
        - ~#t –> (@class@ <boolean> #t)~
        - ~#f –> (@class@ <boolean> #f)~
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
        - `#*10101 –> (@class@ <bitvector> #*10101)`
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

** Phase 2 – Type System Work

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
          - [Typed quote / antiquote][typed-quote-antiquote]
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
    - [ ] Typecheck all of `ice-9`
      - [ ] `(ice-9 and-let-star)`
      - [ ] `(ice-9 binary-ports)`
      - [ ] `(ice-9 boot-9)`
      - [ ] `(ice-9 buffered-input)`
      - [ ] `(ice-9 calling)`
      - [ ] `(ice-9 channel)`
      - [ ] `(ice-9 command-line)`
      - [ ] `(ice-9 common-list)`
      - [ ] `(ice-9 control)`
      - [ ] `(ice-9 curried-definitions)`
      - [ ] `(ice-9 debug)`
      - [ ] `(ice-9 deprecated)`
      - [ ] `(ice-9 documentation)`
      - [ ] `(ice-9 eval)`
      - [ ] `(ice-9 eval-string)`
      - [ ] `(ice-9 expect)`
      - [ ] `(ice-9 format)`
      - [ ] `(ice-9 ftw)`
      - [ ] `(ice-9 futures)`
      - [ ] `(ice-9 gap-buffer)`
      - [ ] `(ice-9 getopt-long)`
      - [ ] `(ice-9 hash-table)`
      - [ ] `(ice-9 hcons)`
      - [ ] `(ice-9 history)`
      - [ ] `(ice-9 i18n)`
      - [ ] `(ice-9 iconv)`
      - [ ] `(ice-9 lineio)`
      - [ ] `(ice-9 list)`
      - [ ] `(ice-9 local-eval)`
      - [ ] `(ice-9 ls)`
      - [ ] `(ice-9 mapping)`
      - [ ] `(ice-9 match)`
      - [ ] `(ice-9 match.upstream)`
      - [ ] `(ice-9 networking)`
      - [ ] `(ice-9 null)`
      - [ ] `(ice-9 occam-channel)`
      - [ ] `(ice-9 optargs)`
      - [ ] `(ice-9 poe)`
      - [ ] `(ice-9 poll)`
      - [ ] `(ice-9 popen)`
      - [ ] `(ice-9 posix)`
      - [ ] `(ice-9 pretty-print)`
      - [ ] `(ice-9 psyntax-pp)`
      - [ ] `(ice-9 psyntax)`
      - [ ] `(ice-9 q)`
      - [ ] `(ice-9 quasisyntax)`
      - [ ] `(ice-9 r4rs)`
      - [ ] `(ice-9 r5rs)`
      - [ ] `(ice-9 r6rs-libraries)`
      - [ ] `(ice-9 rdelim)`
      - [ ] `(ice-9 readline)`
      - [ ] `(ice-9 receive)`
      - [ ] `(ice-9 regex)`
      - [ ] `(ice-9 runq)`
      - [ ] `(ice-9 rw)`
      - [ ] `(ice-9 safe-r5rs)`
      - [ ] `(ice-9 safe)`
      - [ ] `(ice-9 save-stack)`
      - [ ] `(ice-9 scm-style-repl)`
      - [ ] `(ice-9 serialize)`
      - [ ] `(ice-9 session)`
      - [ ] `(ice-9 slib)`
      - [ ] `(ice-9 stack-catch)`
      - [ ] `(ice-9 streams)`
      - [ ] `(ice-9 string-fun)`
      - [ ] `(ice-9 syncase)`
      - [ ] `(ice-9 threads)`
      - [ ] `(ice-9 time)`
      - [ ] `(ice-9 top-repl)`
      - [ ] `(ice-9 vlist)`
      - [ ] `(ice-9 weak-vector)`

** Phase 3 – Porting to Typed Guile

- [ ] Port the type checker to Typed Guile.

** Phase 4 – Guile Compiler Integration

- [ ] Integrate the Guile typechecker into the Guile compiler.
- [ ] Port the Guile compiler to Typed Guile.
- Typed Guile should be self-hosting at this point.

** Phase 5 – Tooling

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

* Design Decisions

** Architecture

*** Parsing

- We should use [derivative parsers][derp] in general (though we will probably
  wait until we have ported, i.e.: after phase 2).
- We should use [megaparsec][] for easy error reporting and correctness.
  - It would be cool to have something like megaparsec, but based on derivative
    parsing, though it's not clear what the tradeoffs are there.

*** Compilation

**** Nanopass Compilation

- We should use a "nanopass"-style compiler, with many small passes rather than
  a few large, complex passes.
  - Nanopass is native to the Scheme world, and there are some existing untyped
    implementations of a so-called "nanopass framework" in
    - [Chez Scheme / Ikarus Scheme / Vicare Scheme][nanopass-original]
    - [Racket][nanopass-racket]
  - Here is a decent series of blog posts on nanopass in Haskell:
    [1][nanopass-blog-1], [2][nanopass-blog-2],
    [3][nanopass-blog-3], [4][nanopass-blog-4]
  - There are type-related challenges in implementing nanopass properly for
    which the following links may be relevant:
    - [Scrap Your Boilerplate][syb-papers]
    - [Data Types à la Carte][data-types-a-la-carte]
    - [Variations on Variants][variations-on-variants]

**** Passes

- We start with a ~ByteString~ read in by the system.
- This ~ByteString~ consists of the contents of every 
- The `…` means that the input type is the same as the output type of the last
  pass performed.

|--------------------+---------------+-----------------------------------------|
| Name               | Type          | Description                             |
|--------------------+---------------+-----------------------------------------|
| Read input files   | ~[BS]~        | Read the given source file and all      |
|                    |               | source files in the current load        |
|                    |               | path. Laziness will be good here;       |
|                    |               | if we strictly read the main file       |
|                    |               | but lazily read all the other files,    |
|                    |               | we will be able to avoid the memory,    |
|                    |               | IO, and CPU cost of reading every       |
|                    |               | file in the load path when only a       |
|                    | *IO*          | fraction will actually be requested.    |
|--------------------+---------------+-----------------------------------------|
| Format heuristics  | ~(BS, Codec)~ | Speculatively decode the file and       |
|                    |               | search for an Emacs-style coding        |
|                    |               | attribute. If found, determine the      |
|                    |               | corresponding codec and attach it       |
|                    |               | to the given ~ByteString~.              |
|                    |               |                                         |
|                    |               | Otherwise, use other heuristics to      |
|                    |               | figure out the file format.             |
|                    |               |                                         |
|                    |               | If all else fails, error and ask        |
|                    |               | the user to provide an Emacs            |
|                    | *Analysis*    | coding attribute.                       |
|--------------------+---------------+-----------------------------------------|
| Text decoding      | ~UTF-8~       | Decode the given bytes to UTF-8.        |
|                    | *Transform*   |                                         |
|--------------------+---------------+-----------------------------------------|
| Unicode expansion  | ~UTF-32~      | Expand UTF-8 to a good fixed-width      |
|                    |               | encoding like UTF-32, so location       |
|                    | *Transform*   | analysis will be far easier.            |
|--------------------+---------------+-----------------------------------------|
| Tokenization       | ~[Token]~     | Split the given text into tokens        |
|                    | *Transform*   | representing syntax.                    |
|--------------------+---------------+-----------------------------------------|
| Location analysis  | ~[LToken]~    | Annotate each token with a source       |
|                    | *Transform*   | location or range.                      |
|--------------------+---------------+-----------------------------------------|
| Parsing            | ~AST~         | Generate an AST equivalent to the sexpr |
|                    |               | of the Guile source, except with token  |
|                    |               | location information added.             |
|                    | *Transform*   |                                         |
|--------------------+---------------+-----------------------------------------|
| Quasiquote desugar | ~AST~         | Replace all uses of `(unquote ...)` and |
|                    | *Desugar*     | `(quasiquote ...)` with the equivalent  |
|                    |               | uses of `(list ...)`.                   |
|--------------------+---------------+-----------------------------------------|

|--------------------+---------------+-----------------------------------------|
| Primitive macro    | ~AST~         | Find all macros defined with the macro  |
| detection          |               | creation primitives, and replace them   |
|                    |               | with ~Macro~ structures, and add them   |
|                    |               | to a global list of macros.             |
|                    |               |                                         |
|                    | *Transform*   | Default the macros to Phase 2 eval.     |
|--------------------+---------------+-----------------------------------------|
| Meta-macro         | ~AST~         | Set all macros that contain a macro     |
| detection          |               | creation primitive in their definitions |
|                    | *Transform*   | to Phase 1 evaluation.                  |
|--------------------+---------------+-----------------------------------------|
|--------------------+---------------+-----------------------------------------|
| Binder detection   | ~AST~         |                                         |
|--------------------+---------------+-----------------------------------------|
| Binder annotation  | ~AST~         | Any time a variable is introduced       |
|                    |               | or referenced, add a tag showing        |
|                    | *Annotate*    | that fact.                              |
|--------------------+---------------+-----------------------------------------|
| Variable numbering | Side effect   | Traverse the AST,                       |
|                    | *Analysis*    |                                         |
|--------------------+---------------+-----------------------------------------|
| Renamer generation | Side effect   |                                         |
|                    | *Analysis*    |                                         |
|--------------------+---------------+-----------------------------------------|
| Alpha renaming     | ~AST~         | Number each variable name and create    |
|                    |               | a deterministic finite automaton        |
|                    |               | that will crawl the AST and replace     |
|                    |               | each instance of a variable with its    |
|                    |               | identification number.                  |
|                    |               |                                         |
|                    |               | Save the identification number to       |
|                    |               | variable name mapping in a global       |
|                    |               | store, so we can have sane error        |
|                    | *Transform*   | messages later.                         |
|--------------------+---------------+-----------------------------------------|
| Scope analysis     | ~AST~         | Scan the program, determining the       |
|                    |               | scope at every point a variable is      |
|                    |               | referenced or introduced. Add this      |
|                    | *Analysis*    | to a global table.                      |
|--------------------+---------------+-----------------------------------------|
|                    | ~AST~         |                                         |
|                    | *Transform*   |                                         |
|--------------------+---------------+-----------------------------------------|
|                    |               |                                         |
  
** Type system

*** Let

- I think we probably should not do let generalization. Obviously, we will have
  to have some structure capability of introducing polymorphic bound variables,
  but I think that in general let generalization is probably not the way to go.
  - This view is supported in [this paper][dont-generalize-let].
- On the other hand, it's definitely not clear how

*** Continuations

- Luckily, `call-with-current-continuation` is quite rare in Guile.
  - It is only used a few times in the Guile compiler.
- Delimited continuations (as defined in `(ice-9 control)`) are, however, used
  quite a few times.
- Perhaps we could type these with the [Cont monad][cont-monad].

*** Typeclasses

- Relevant papers:
  - [Maintainable Type Classes for Haskell][maintain-tc]

*** Effects

- Should we go with monadic IO or uniqueness typing?
- For layering of effects, should we use monad transformers, algebraic effects,
  or extensible effects? What about labelled IO?
- What are the tradeoffs here vis-à-vis usability, learnability, expressiveness,
  type system complexity?
- Relevant papers:
  - [Algebraic Effects in Idris][idris-alg]
  - [Uniqueness Types in Idris][idris-uniq]
  - [RWH: Monad Transformers][rwh-monad-transformers]
  - [Extensible Effects: An Alternative to Monad Transformers][exteff]
  - [Freer Monads, More Extensible Effects][more-exteff]
  - [The effects package in Hackage][hackage-effects]
  - [Labelled IO][hackage-lio]

*** Concurrency

- [Session Types Without Class][session-types-without-class]
- [Implicit parallelism][implicit-parallelism] is interesting.
  - Needs higher-order specialization (defunctionalization) to be effective.

** Typing Guile semantics

*** Functions

- Should functions be curried in the type system, despite not being curried in
  the operational semantics of Scheme?
- Keyword/Rest Arguments
  - We should type keyword and rest arguments by translating to HM types.
  - There are a variety of ways to type keywords and rest arguments, most of
    which are listed [here][polyvariadic].

*** Objects

- I think we can mostly type GOOPS classes as being open type classes.
  - Basically, any time a class is declared, create a type class, and then add
    a method to that type class for every unique generic method that takes a
    thing with that type.
  - Whenever you encounter polymorphism (i.e.: two generic methods with the same
    name and different types), encode that as an instance of the typeclass.
  - It may actually be worth it to expose open type classes as a user-accessible
    feature outside of type system hackery.
- Perhaps we could use [subtypes][subtyping]?
- Related: [MLsub][mlsub].

** Other decisions

*** Modules

- Should we bother typing modules?
- The [1ML system][] is rather promising for typing modules.
- [Backpack][] is also interesting and worth looking at.

*** Tooling

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
- Proving laws can be improved with [Hermit][hermit].
- A Guile project generator, à la `cabal init`, would be very nice.
  - It should generate all of the following files:
    - FIXME

*** Misc

- Relevant papers:
  - [Strong Static Type Checking for Functional Common Lisp][typing-clisp]

#+LINK:
  Tandoori
  http://gergo.erdi.hu/projects/tandoori/
#+LINK:
  1ML system
  http://www.mpi-sws.org/~rossberg/1ml/
#+LINK:
  guile-lint
  http://user42.tuxfamily.org/guile-lint/
#+LINK:
  elm-errors
  http://elm-lang.org/blog/compiler-errors-for-humans
#+LINK:
  maintain-tc
  http://ff32.host.cs.st-andrews.ac.uk/papers/hsym15.pdf
#+LINK:
  idris-uniq
  http://idris.readthedocs.org/en/latest/reference/uniqueness-types.html
#+LINK:
  idris-alg
  http://eb.host.cs.st-andrews.ac.uk/drafts/effects.pdf
#+LINK:
  polyvariadic
  http://okmij.org/ftp/Haskell/polyvariadic.html
#+LINK:
  boxes
  http://hackage.haskell.org/package/boxes
#+LINK:
  vty-ui
  http://hackage.haskell.org/package/vty-ui
#+LINK:
  brick
  http://hackage.haskell.org/package/brick
#+LINK:
  exteff
  http://okmij.org/ftp/Haskell/extensible/exteff.pdf
#+LINK:
  more-exteff
  http://okmij.org/ftp/Haskell/extensible/more.pdf
#+LINK:
  rwh-monad-transformers
  http://book.realworldhaskell.org/read/monad-transformers.html#id6594
#+LINK:
  Haskell
  http://haskell.org
#+LINK:
  Typed Racket
  http://docs.racket-lang.org/ts-guide/index.html
#+LINK:
  Typed Clojure
  http://github.com/clojure/core.typed
#+LINK:
  SML
  http://sml-family.org
#+LINK:
  OCaml
  http://caml.inria.fr/pub/docs/manual-ocaml/
#+LINK:
  derp
  http://hackage.haskell.org/package/derp
#+LINK:
  prof-type
  http://www.cs.umd.edu/projects/PL/druby/papers/druby-tr-4935.pdf
#+LINK:
  cont-monad
  http://hackage.haskell.org/package/mtl/docs/Control-Monad-Cont.html
#+LINK:
  hackage-effects
  http://hackage.haskell.org/package/effects
#+LINK:
  hackage-lio
  http://hackage.haskell.org/package/lio
#+LINK:
  guile-bool
  http://www.gnu.org/software/guile/manual/html_node/Booleans.html
#+LINK:
  guile-num
  http://www.gnu.org/software/guile/manual/html_node/Numbers.html
#+LINK:
  guile-char
  http://www.gnu.org/software/guile/manual/html_node/Characters.html
#+LINK:
  guile-str
  http://www.gnu.org/software/guile/manual/html_node/Strings.html
#+LINK:
  guile-sym
  http://www.gnu.org/software/guile/manual/html_node/Symbols.html
#+LINK:
  guile-kw
  http://www.gnu.org/software/guile/manual/html_node/Keywords.html
#+LINK:
  guile-vec
  http://www.gnu.org/software/guile/manual/html_node/Vectors.html
#+LINK:
  guile-arr
  http://www.gnu.org/software/guile/manual/html_node/Arrays.html
#+LINK:
  guile-bv
  http://www.gnu.org/software/guile/manual/html_node/Bytevectors.html
#+LINK:
  guile-bits
  http://www.gnu.org/software/guile/manual/html_node/Bit-Vectors.html
#+LINK:
  catch-totality
  http://community.haskell.org/~ndm/catch/
#+LINK:
  liquid-haskell
  http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about
#+LINK:
  herbie
  http://herbie.uwplse.org
#+LINK:
  herbie-ghc
  http://github.com/mikeizbicki/HerbiePlugin
#+LINK:
  GADTs meet their match
  http://research.microsoft.com/en-us/um/people/simonpj/papers/pattern-matching/gadtpm.pdf
#+LINK:
  z3-prover
  http://github.com/Z3Prover/z3
#+LINK:
  rosette
  http://homes.cs.washington.edu/~emina/rosette/guide/index.html
#+LINK:
  Backpack
  http://plv.mpi-sws.org/backpack
#+LINK:
  implicit-parallelism
  http://www.youtube.com/watch?v=UsU8h0WYemo
#+LINK:
  subtyping
  http://www21.in.tum.de/~nipkow/pubs/aplas11.pdf
#+LINK:
  typing-clisp
  ftp://ftp.cs.utexas.edu/pub/boyer/diss/akers.pdf
#+LINK:
  session-types-without-class
  http://users.eecs.northwestern.edu/~jesse/pubs/haskell-session-types/session08.pdf
#+LINK:
  mlsub
  http://github.com/stedolan/mlsub
#+LINK:
  hermit
  http://hackage.haskell.org/package/hermit
#+LINK:
  typed-quote-antiquote
  http://www.cs.ox.ac.uk/people/ralf.hinze/publications/Quote.pdf
#+LINK:
  dont-generalize-let
  http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/let-gen.pdf
#+LINK:
  megaparsec
  http://hackage.haskell.org/package/megaparsec
#+LINK:
  nanopass-blog-1
  http://merrycomputing.blogspot.com/2015/08/a-nanopass-compiler-in-haskell.html
#+LINK:
  nanopass-blog-2
  http://merrycomputing.blogspot.com/2015/08/a-nanopass-compiler-in-haskell-part-2.html
#+LINK:
  nanopass-blog-3
  http://merrycomputing.blogspot.com/2015/09/a-nanopass-compiler-in-haskell-part-3.html
#+LINK:
  nanopass-blog-4
  http://merrycomputing.blogspot.com/2015/09/a-nanopass-compiler-in-haskell-part-4.html
#+LINK:
  nanopass-original
  http://github.com/akeep/nanopass-framework
#+LINK:
  nanopass-racket
  http://github.com/LeifAndersen/nanopass-framework-racket
#+LINK:
  data-types-a-la-carte
  http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.101.4131
#+LINK:
  compdata
  http://hackage.haskell.org/package/compdata
#+LINK:
  syb-papers
  http://research.microsoft.com/en-us/um/people/simonpj/papers/hmap/
#+LINK:
  variations-on-variants
  http://homepages.inf.ed.ac.uk/jmorri14/pubs/morris-haskell15-variants.pdf
#+LINK:
  typeclass-impl
  http://okmij.org/ftp/Computation/typeclass.html
