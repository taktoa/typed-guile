# Roadmap

## Phase 1 - Implementation in Haskell

* Write a type checker for Guile in Haskell.
  * Fix [Tandoori][] such that it can successfully typecheck Haskell.

## Phase 2 - Porting to Typed Guile

* Port the type checker to Typed Guile.

## Phase 3 - Guile Compiler Integration

* Integrate the Guile typechecker into the Guile compiler.
* Port the Guile compiler to Typed Guile.
* Typed Guile should be self-hosting at this point.

# Design Decisions

## Parsing

* We should use [derivative parsers][derp] in general (though we will probably
  wait until we have ported, i.e.: after phase 2).

## Type system

### Typeclasses

* Relevant papers:
  * [Maintainable Type Classes for Haskell][maintain-tc]

### Effects

* Should we go with monadic IO or uniqueness typing?
* For layering of effects, should we use monad transformers, algebraic effects,
  or extensible effects?
* What are the tradeoffs here vis-à-vis usability, learnability, expressiveness,
  type system complexity?
* Relevant papers:
  * [Algebraic Effects in Idris][idris-alg]
  * [Uniqueness Types in Idris][idris-uniq]
  * [RWH: Monad Transformers][rwh-monad-transformers]
  * [Extensible Effects: An Alternative to Monad Transformers][exteff]
  * [Freer Monads, More Extensible Effects][more-exteff]

## Typing Guile semantics

### Functions

* Should functions be curried in the type system, despite not being curried in 
  the operational semantics of Scheme?
* Keyword/Rest Arguments
  * We should type keyword and rest arguments by translating to HM types.
  * There are a variety of ways to type keywords and rest arguments, most of
    which are listed [here][polyvariadic].

### Objects

* I think we can mostly type GOOPS classes as being open type classes.
  * Basically, any time a class is declared, create a type class, and then add
    a method to that type class for every unique generic method that takes a
    thing with that type.
  * Whenever you encounter polymorphism (i.e.: two generic methods with the same
    name and different types), encode that as an instance of the typeclass.
  * It may actually be worth it to expose open type classes as a user-accessible
    feature outside of type system hackery.

## Other decisions

### Modules

* Should we bother typing modules?
* The [1ML system][] is rather promising for typing modules.

### Tooling

* We should fix [guile-lint][guile-lint]
* We should make a usable terminal UI for Guile, à la [Elm][elm-errors].
  * It would be neat to make it even fancier with a powerline-style top bar.
  * Writing a library for ANSI colors etc. in Guile would be useful.
  * Porting [boxes][], [vty-ui][], or [brick][] could also be useful.
* Profile-guided after-the-fact typing would be very useful for translating the
  Guile compiler (and other untyped Guile libraries) to Typed Guile.
  * [Profile-Guided Static Typing for Dynamic Scripting Languages][prof-type]
* We should have automatic tools for translating [Haskell][], [Typed Racket][], 
  [Typed Clojure][], [SML][], and [OCaml][] to Typed Guile (or, at the very 
  least, have tools for importing type signatures).

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
  https://eb.host.cs.st-andrews.ac.uk/drafts/effects.pdf
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
  https://github.com/clojure/core.typed
[SML]:
  http://sml-family.org
[OCaml]:
  http://caml.inria.fr/pub/docs/manual-ocaml/
[derp]:
  http://hackage.haskell.org/package/derp
[prof-type]:
  http://www.cs.umd.edu/projects/PL/druby/papers/druby-tr-4935.pdf
