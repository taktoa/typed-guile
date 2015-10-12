.. -*- mode: rst; coding: utf-8 -*-

Roadmap
-------

Phase 1 – Implementation in Haskell
===================================

- Write a type checker for Guile in Haskell.

  - Fix Tandoori_ such that it can successfully typecheck Haskell.
  - Write a program that normalizes the syntax of Guile to be easily parsed
    by a Haskell parser.

    - Run Guile reader on input.
    - Annotate syntax information to include line numbers concretely.
    - Annotate syntax with available type information
      (i.e.: add types to literals).
    - Do scope analysis and create an AST populated exclusively with
      fully-qualified (vis-à-vis modules) unique identifiers
    - Write normalizers for various built-in types using GOOPS ``class-of``

      - Booleans_:

        - ``#t –> (@class@ <boolean> #t)``
        - ``#f –> (@class@ <boolean> #f)``

      - Numbers_:

        - ``534 –> (@class@ <integer> 534)``
        - ``5/6 –> (@class@ <fraction> 5/6)``
        - ``5.3 –> (@class@ <real> 5.3)``

      - Characters_:

        - ``#\b –> (@class@ <char> #\b)``

      - Strings_:

        - ``"hello" –> (@class@ <string> "hello")``

      - Symbols_:

        - ``'hello –> (@class@ <symbol> 'hello)``

      - Keywords_:

        - ``#:example –> (@class@ <keyword> #:example)``

      - Vectors_:

        - ``#(1 2 3) –> (@class@ <vector> #(1 2 3))``

      - Arrays_:

        - ``#@2(1 2 3) –> (@class@ <array> #@2(1 2 3))``

      - Bytevectors_:

        - ``#vu8(1 53 204) –> (@class@ <bytevector> 1 53 204)``

      - Bitvectors_:

        - ``#*10101 –> (@class@ <bitvector> #*10101)``

      - Docstrings: run the ``texinfo`` parser on all docstrings.

    - Write test cases for the normalizer using SRFI-64.

  - Write a Haskell module that launches Guile to normalize an input string.
  - Make a parser in Haskell for s-expressions (should return a rose tree).
  - Make a GADT representing the annotated Guile AST.
  - Write a function that takes the rose tree and outputs the typed tree.
  - Abstract out the GHC API from Tandoori.
  - Wire together the Tandoori code and the typed Guile AST.
  - Successfully type basic arithmetic expressions in Guile.

.. _Tandoori:
   http://gergo.erdi.hu/projects/tandoori/
.. _Booleans:
   http://www.gnu.org/software/guile/manual/html_node/Booleans.html
.. _Numbers:
   http://www.gnu.org/software/guile/manual/html_node/Numbers.html
.. _Characters:
   http://www.gnu.org/software/guile/manual/html_node/Characters.html
.. _Strings:
   http://www.gnu.org/software/guile/manual/html_node/Strings.html
.. _Symbols:
   http://www.gnu.org/software/guile/manual/html_node/Symbols.html
.. _Keywords:
   http://www.gnu.org/software/guile/manual/html_node/Keywords.html
.. _Vectors:
   http://www.gnu.org/software/guile/manual/html_node/Vectors.html
.. _Arrays:
   http://www.gnu.org/software/guile/manual/html_node/Arrays.html
.. _Bytevectors:
   http://www.gnu.org/software/guile/manual/html_node/Bytevectors.html
.. _Bitvectors:
   http://www.gnu.org/software/guile/manual/html_node/Bit-Vectors.html

Phase 2 – Type System Work
==========================

- Write typing judgments and test cases for a lot of code.
- Benchmarks:

  - Typecheck code involving:

    - Monomorphic types

      - Booleans
      - Numbers
      - Characters
      - Strings
      - Bitvectors
      - Bytevectors
      - Quasiquoting

        - `Typed quote / antiquote`_

      - ``*unspecified*``

    - Polymorphic types

      - Lists

        - Homogeneous lists
        - Heterogeneous lists

      - Vectors
      - Arrays
      - Hash tables

    - Complex types

      - Modules
      - Objects

    - Type signatures

      - Prefix syntax
      - Infix syntax
      - Top-level
      - Inline
      - Scoped type variables

    - Algebraic data types

      - Enumerated types
      - Polymorphic ADTs
      - GADTs

    - Typeclasses

      - Class definitions
      - Instances
      - Multi-parameter type classes
      - Flexible instances
      - Functional dependencies
      - Maintainable type classes

    - Control flow

      - Conditional

        - ``if``
        - ``cond``
        - ``when`` / ``unless``
        - ``case``
        - ``match``

      - Iteration

        - ``do``
        - ``while``
        - Named ``let``

    - Nonlinear program flow

      - Continuations

        - Prompts

          - ``call-with-prompt``
          - ``make-prompt-tag``
          - ``default-prompt-tag``
          - ``abort-to-prompt``

        - Escape

          - ``call-with-escape-continuation``
          - ``let-escape-continuation``

        - Delimited

          - ``shift`` / ``reset``

        - Unrestricted

          - ``call-with-current-continuation``
          - ``dynamic-wind``

      - Exceptions
      - Signals
      - Parameters
      - Continuation barriers

  - Functions

    - Single-argument
    - Nullary
    - Multiple arguments
    - Rest arguments
    - Keyword arguments

  - Binding

    - Local

      - ``let``
      - ``let*``
      - ``letrec``
      - ``letrec*``

    - Global

      - ``define`` for values
      - ``define`` for functions
      - ``define*``

  - Macros

    - ``define-syntax-rule``
    - Hygienic macros
    - Procedural macros

  - Typecheck Guile compiler.

  - Typecheck all Guile SRFIs.

    - SRFI-0:   ``cond-expand``
    - SRFI-1:   List library
    - SRFI-2:   ``and-let*``
    - SRFI-4:   Homogeneous numeric vector datatypes
    - SRFI-6:   Basic string ports
    - SRFI-8:   ``receive``
    - SRFI-9:   ``define-record-type``
    - SRFI-10:  Hash-comma reader extension
    - SRFI-11:  ``let-values``
    - SRFI-13:  String library
    - SRFI-14:  Character-set library
    - SRFI-16:  ``case-lambda``
    - SRFI-17:  Generalized ``set!``
    - SRFI-18:  Multithreading support
    - SRFI-19:  Time/Date library
    - SRFI-23:  Error reporting
    - SRFI-26:  Specializing parameters
    - SRFI-27:  Sources of random bits
    - SRFI-30:  Nested multi-line comments
    - SRFI-31:  Recursive evaluation
    - SRFI-34:  Exception handling for programs
    - SRFI-35:  Conditions
    - SRFI-37:  ``args-fold``
    - SRFI-38:  Abstract binding syntax
    - SRFI-39:  Parameters
    - SRFI-41:  Streams
    - SRFI-42:  Eager comprehensions
    - SRFI-43:  Vector library
    - SRFI-45:  Iterative lazy algorithm primitives
    - SRFI-46:  Basic ``syntax-rules`` extensions
    - SRFI-55:  Requiring features
    - SRFI-60:  Integers as bits
    - SRFI-61:  A more general ``cond`` clause
    - SRFI-62:  Comments in s-expressions
    - SRFI-64:  Test suites
    - SRFI-67:  Comparison procedures
    - SRFI-69:  Basic hash tables
    - SRFI-87:  ``=>`` in ``case`` clauses
    - SRFI-88:  Keywords
    - SRFI-98:  Accessing environment variables
    - SRFI-105: Curly-infix expressions
    - SRFI-111: Boxes

  - Typecheck all of ``ice-9``

    - ``(ice-9 and-let-star)``
    - ``(ice-9 binary-ports)``
    - ``(ice-9 boot-9)``
    - ``(ice-9 buffered-input)``
    - ``(ice-9 calling)``
    - ``(ice-9 channel)``
    - ``(ice-9 command-line)``
    - ``(ice-9 common-list)``
    - ``(ice-9 control)``
    - ``(ice-9 curried-definitions)``
    - ``(ice-9 debug)``
    - ``(ice-9 deprecated)``
    - ``(ice-9 documentation)``
    - ``(ice-9 eval)``
    - ``(ice-9 eval-string)``
    - ``(ice-9 expect)``
    - ``(ice-9 format)``
    - ``(ice-9 ftw)``
    - ``(ice-9 futures)``
    - ``(ice-9 gap-buffer)``
    - ``(ice-9 getopt-long)``
    - ``(ice-9 hash-table)``
    - ``(ice-9 hcons)``
    - ``(ice-9 history)``
    - ``(ice-9 i18n)``
    - ``(ice-9 iconv)``
    - ``(ice-9 lineio)``
    - ``(ice-9 list)``
    - ``(ice-9 local-eval)``
    - ``(ice-9 ls)``
    - ``(ice-9 mapping)``
    - ``(ice-9 match)``
    - ``(ice-9 match.upstream)``
    - ``(ice-9 networking)``
    - ``(ice-9 null)``
    - ``(ice-9 occam-channel)``
    - ``(ice-9 optargs)``
    - ``(ice-9 poe)``
    - ``(ice-9 poll)``
    - ``(ice-9 popen)``
    - ``(ice-9 posix)``
    - ``(ice-9 pretty-print)``
    - ``(ice-9 psyntax-pp)``
    - ``(ice-9 psyntax)``
    - ``(ice-9 q)``
    - ``(ice-9 quasisyntax)``
    - ``(ice-9 r4rs)``
    - ``(ice-9 r5rs)``
    - ``(ice-9 r6rs-libraries)``
    - ``(ice-9 rdelim)``
    - ``(ice-9 readline)``
    - ``(ice-9 receive)``
    - ``(ice-9 regex)``
    - ``(ice-9 runq)``
    - ``(ice-9 rw)``
    - ``(ice-9 safe-r5rs)``
    - ``(ice-9 safe)``
    - ``(ice-9 save-stack)``
    - ``(ice-9 scm-style-repl)``
    - ``(ice-9 serialize)``
    - ``(ice-9 session)``
    - ``(ice-9 slib)``
    - ``(ice-9 stack-catch)``
    - ``(ice-9 streams)``
    - ``(ice-9 string-fun)``
    - ``(ice-9 syncase)``
    - ``(ice-9 threads)``
    - ``(ice-9 time)``
    - ``(ice-9 top-repl)``
    - ``(ice-9 vlist)``
    - ``(ice-9 weak-vector)``

.. _Typed quote / antiquote:
   http://www.cs.ox.ac.uk/people/ralf.hinze/publications/Quote.pdf

Phase 3 – Porting to Typed Guile
================================

- Port the type checker to Typed Guile.

Phase 4 – Guile Compiler Integration
====================================

- Integrate the Guile typechecker into the Guile compiler.
- Port the Guile compiler to Typed Guile.
- Typed Guile should be self-hosting at this point.

Phase 5 – Tooling
=================

- Make an exhaustiveness checker for pattern matching.

  - `GADTs meet their match`_

- Implement refinement types.

  - `Liquid Haskell`_
  - `Z3 Prover`_
  - `Rosette`_

- Make a totality checker.

  - `Catch: Case Totality Checker for Haskell`_

- Make a numerical stability linter.

  - `Herbie`_
  - `Herbie GHC Plugin`_

- Work on ``guildhall``, the Guile package manager.

  - Make the ``guildhall`` website: https://guildhall.io

- Fix guile-lint_.
- Make profile-guided typing tool.

.. _GADTs meet their match:
   http://research.microsoft.com/en-us/um/people/simonpj/papers/pattern-matching/gadtpm.pdf
.. _Liquid haskell:
   http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/about
.. _Z3 Prover:
   http://github.com/Z3Prover/z3
.. _Rosette:
   http://homes.cs.washington.edu/~emina/rosette/guide/index.html
.. _Catch\: Case Totality Checker for Haskell:
   http://community.haskell.org/~ndm/catch/
.. _Herbie:
   http://herbie.uwplse.org
.. _Herbie GHC Plugin:
   http://github.com/mikeizbicki/HerbiePlugin
.. _guile-lint:
   http://user42.tuxfamily.org/guile-lint/

Design Decisions
----------------

Architecture
============

Parsing
~~~~~~~

- We should use `derivative parsers`_ in general (though we will probably wait
  until we have ported, i.e.: after phase 2).
- We should use megaparsec_ for easy error reporting and correctness.

  - It would be cool to have something like megaparsec, but based on derivative
    parsing, though it's not clear what the tradeoffs are there.

.. _derivative parsers:
   http://hackage.haskell.org/package/derp
.. _megaparsec:
   http://hackage.haskell.org/package/megaparsec

Compilation
~~~~~~~~~~~

Nanopass Compilation
^^^^^^^^^^^^^^^^^^^^

- We should use a "nanopass"-style compiler, with many small passes rather than
  a few large, complex passes.

  - Nanopass is native to the Scheme world, and there are some existing untyped
    implementations of a so-called "nanopass framework" in

    - `Nanopass in Chez Scheme / Ikarus Scheme / Vicare Scheme`_
    - `Nanopass in Racket`_

  - Here is a decent series of blog posts on nanopass in Haskell:

    - `Nanopass Blog Post 1`_
    - `Nanopass Blog Post 2`_
    - `Nanopass Blog Post 3`_
    - `Nanopass Blog Post 4`_

  - There are type-related challenges in implementing nanopass properly for
    which the following links may be relevant:

    - `Scrap Your Boilerplate`_
    - `Data Types à la Carte`_
    - `Variations on Variants`_

.. _Nanopass in Chez Scheme / Ikarus Scheme / Vicare Scheme:
   http://github.com/akeep/nanopass-framework
.. _Nanopass in Racket:
   http://github.com/LeifAndersen/nanopass-framework-racket
.. _Nanopass Blog Post 1:
   http://merrycomputing.blogspot.com/2015/08/a-nanopass-compiler-in-haskell.html
.. _Nanopass Blog Post 2:
   http://merrycomputing.blogspot.com/2015/08/a-nanopass-compiler-in-haskell-part-2.html
.. _Nanopass Blog Post 3:
   http://merrycomputing.blogspot.com/2015/09/a-nanopass-compiler-in-haskell-part-3.html
.. _Nanopass Blog Post 4:
   http://merrycomputing.blogspot.com/2015/09/a-nanopass-compiler-in-haskell-part-4.html
.. _Scrap Your Boilerplate:
   http://research.microsoft.com/en-us/um/people/simonpj/papers/hmap/
.. _Data Types à la Carte:
   http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.101.4131
.. _Variations on Variants:
   http://homepages.inf.ed.ac.uk/jmorri14/pubs/morris-haskell15-variants.pdf

Passes
^^^^^^

- **NOTE: this section needs major work**
- We start with a ``ByteString`` read in by the system.

+--------------------+---------------+-----------------------------------------+
| Name               | Type          | Description                             |
+====================+===============+=========================================+
| Read input files   | ``[BS]``      | Read the given source file and all      |
|                    |               | source files in the current load        |
|                    |               | path. Laziness will be good here;       |
|                    |               | if we strictly read the main file       |
|                    |               | but lazily read all the other files,    |
|                    |               | we will be able to avoid the memory,    |
|                    |               | IO, and CPU cost of reading every       |
|                    |               | file in the load path when only a       |
|                    | *IO*          | fraction will actually be requested.    |
+--------------------+---------------+-----------------------------------------+
| Format heuristics  | ``BS``        | Speculatively decode the file and       |
|                    |               | search for an Emacs-style coding        |
|                    |               | attribute. If found, determine the      |
|                    |               | corresponding codec and attach it       |
|                    |               | to the given ``ByteString``.            |
|                    |               |                                         |
|                    |               | Otherwise, use other heuristics to      |
|                    |               | figure out the file format.             |
|                    |               |                                         |
|                    |               | If all else fails, error and ask        |
|                    |               | the user to provide an Emacs            |
|                    | *Analysis*    | coding attribute.                       |
+--------------------+---------------+-----------------------------------------+
| Text decoding      | ``UTF-8``     | Decode the given bytes to UTF-8.        |
|                    | *Transform*   |                                         |
+--------------------+---------------+-----------------------------------------+
| Unicode expansion  | ``UTF-32``    | Expand UTF-8 to a good fixed-width      |
|                    |               | encoding like UTF-32, so location       |
|                    | *Transform*   | analysis will be far easier.            |
+--------------------+---------------+-----------------------------------------+
| Tokenization       | ``[Token]``   | Split the given text into tokens        |
|                    | *Transform*   | representing syntax.                    |
+--------------------+---------------+-----------------------------------------+
| Location analysis  | ``[LToken]``  | Annotate each token with a source       |
|                    | *Transform*   | location or range.                      |
+--------------------+---------------+-----------------------------------------+
| Parsing            | ``AST``       | Generate an AST equivalent to the sexpr |
|                    |               | of the Guile source, except with token  |
|                    |               | location information added.             |
|                    | *Transform*   |                                         |
+--------------------+---------------+-----------------------------------------+
| Quasiquote desugar | ``AST``       | Replace all uses of ``unquote`` and     |
|                    | *Desugar*     | ``quasiquote`` with the equivalent uses |
|                    |               | of ``list``.                            |
+--------------------+---------------+-----------------------------------------+
| Primitive macro    | ``AST``       | Find all macros defined with the macro  |
| detection          |               | creation primitives, and replace them   |
|                    |               | with ``Macro`` structures, and add them |
|                    |               | to a global list of macros.             |
|                    |               |                                         |
|                    | *Transform*   | Default the macros to Phase 2 eval.     |
+--------------------+---------------+-----------------------------------------+
| Meta-macro         | ``AST``       | Set all macros that contain a macro     |
| detection          |               | creation primitive in their definitions |
|                    | *Transform*   | to Phase 1 evaluation.                  |
+--------------------+---------------+-----------------------------------------+
| Binder detection   | ``AST``       |                                         |
+--------------------+---------------+-----------------------------------------+
| Binder annotation  | ``AST``       | Any time a variable is introduced       |
|                    |               | or referenced, add a tag showing        |
|                    | *Annotate*    | that fact.                              |
+--------------------+---------------+-----------------------------------------+
| Variable numbering | Side effect   | Traverse the AST,                       |
|                    | *Analysis*    |                                         |
+--------------------+---------------+-----------------------------------------+
| Renamer generation | Side effect   |                                         |
|                    | *Analysis*    |                                         |
+--------------------+---------------+-----------------------------------------+
| Alpha renaming     | ``AST``       | Number each variable name and create    |
|                    |               | a deterministic finite automaton        |
|                    |               | that will crawl the AST and replace     |
|                    |               | each instance of a variable with its    |
|                    |               | identification number.                  |
|                    |               |                                         |
|                    |               | Save the identification number to       |
|                    |               | variable name mapping in a global       |
|                    |               | store, so we can have sane error        |
|                    | *Transform*   | messages later.                         |
+--------------------+---------------+-----------------------------------------+
| Scope analysis     | ``AST``       | Scan the program, determining the       |
|                    |               | scope at every point a variable is      |
|                    |               | referenced or introduced. Add this      |
|                    | *Analysis*    | to a global table.                      |
+--------------------+---------------+-----------------------------------------+

Type system
===========

Let
~~~

- I think we probably should not do let generalization. Obviously, we will have
  to have some structure capability of introducing polymorphic bound variables,
  but I think that in general let generalization is probably not the way to go.

  - This view is supported in `Let Should Not Be Generalized`_.

- On the other hand, it's definitely not clear how

.. _Let Should Not Be Generalized:
   http://research.microsoft.com/en-us/um/people/simonpj/papers/constraints/let-gen.pdf

Continuations
~~~~~~~~~~~~~

- Luckily, ``call-with-current-continuation`` is quite rare in Guile.

  - It is only used a few times in the Guile compiler.

- Delimited continuations (as defined in ``(ice-9 control)``) are, however, used
  quite a few times.
- Perhaps we could type these with the `Cont monad`_.

.. _Cont monad:
   http://hackage.haskell.org/package/mtl/docs/Control-Monad-Cont.html

Typeclasses
~~~~~~~~~~~

- Relevant papers:

  - `Maintainable Type Classes for Haskell`_

.. _Maintainable Type Classes for Haskell:
   http://ff32.host.cs.st-andrews.ac.uk/papers/hsym15.pdf

Effects
~~~~~~~

- Should we go with monadic IO or uniqueness typing?
- For layering of effects, should we use monad transformers, algebraic effects,
  or extensible effects? What about labelled IO?
- What are the tradeoffs here vis-à-vis usability, learnability, expressiveness,
  type system complexity?
- Relevant papers:

  - `Algebraic Effects in Idris`_
  - `Uniqueness Types in Idris`_
  - `RWH: Monad Transformers`_
  - `Extensible Effects: An Alternative to Monad Transformers`_
  - `Freer Monads, More Extensible Effects`_
  - `The effects package in Hackage`_
  - `Labelled IO`_

.. _Algebraic Effects in Idris:
   http://eb.host.cs.st-andrews.ac.uk/drafts/effects.pdf
.. _Uniqueness Types in Idris:
   http://idris.readthedocs.org/en/latest/reference/uniqueness-types.html
.. _RWH\: Monad Transformers:
   http://book.realworldhaskell.org/read/monad-transformers.html#id6594
.. _Extensible Effects\: An Alternative to Monad Transformers:
   http://okmij.org/ftp/Haskell/extensible/exteff.pdf
.. _Freer Monads, More Extensible Effects:
   http://okmij.org/ftp/Haskell/extensible/more.pdf
.. _The effects package in Hackage:
   http://hackage.haskell.org/package/effects
.. _Labelled IO:
   http://hackage.haskell.org/package/lio

Concurrency
~~~~~~~~~~~

- `Session Types Without Class`_
- `Implicit parallelism`_ is interesting.

  - Needs higher-order specialization (defunctionalization) to be effective.

.. _Session Types Without Class:
   http://users.eecs.northwestern.edu/~jesse/pubs/haskell-session-types/session08.pdf
.. _Implicit parallelism:
   http://www.youtube.com/watch?v=UsU8h0WYemo

Typing Guile semantics
======================

Functions
~~~~~~~~~

- Should functions be curried in the type system, despite not being curried in
  the operational semantics of Scheme?
- Keyword/Rest Arguments

  - We should type keyword and rest arguments by translating to HM types.
  - There are a variety of ways to type keywords and rest arguments, most of
    which are listed here: `Polyvariadic functions and keyword arguments`_.

.. _Polyvariadic functions and keyword arguments:
   http://okmij.org/ftp/Haskell/polyvariadic.html

Objects
~~~~~~~

- I think we can mostly type GOOPS classes as being open type classes.

  - Basically, any time a class is declared, create a type class, and then add
    a method to that type class for every unique generic method that takes a
    thing with that type.
  - Whenever you encounter polymorphism (i.e.: two generic methods with the same
    name and different types), encode that as an instance of the typeclass.
  - It may actually be worth it to expose open type classes as a user-accessible
    feature outside of type system hackery.

- Perhaps we could use `subtypes`_?
- Related: `MLsub`_.

.. _subtypes:
   http://www21.in.tum.de/~nipkow/pubs/aplas11.pdf
.. _MLsub:
   http://github.com/stedolan/mlsub

Other decisions
===============

Modules
~~~~~~~

- Should we bother typing modules?
- The `1ML system`_ is rather promising for typing modules.
- `Backpack`_ is also interesting and worth looking at.

.. _1ML system:
   http://www.mpi-sws.org/~rossberg/1ml/
.. _Backpack:
   http://plv.mpi-sws.org/backpack

Tooling
~~~~~~~

- We should fix `guile-lint`_
- We should make a usable terminal UI for Guile, à la Elm_.

  - It would be neat to make it even fancier with a powerline-style top bar.
  - Writing a library for ANSI colors etc. in Guile would be useful.
  - Porting boxes_, vty-ui_, or brick_ could also be useful.

- Profile-guided after-the-fact typing would be very useful for translating the
  Guile compiler (and other untyped Guile libraries) to Typed Guile.

  - `Profile-Guided Static Typing for Dynamic Scripting Languages`_

- We should have automatic tools for translating Haskell_, `Typed Racket`_,
  `Typed Clojure`_, SML_, and OCaml_ to Typed Guile (or, at the very least,
  have tools for importing type signatures).
- Proving laws can be improved with Hermit_.
- A Guile project generator, à la ``cabal init``, would be very nice.

.. _guile-lint:
   http://user42.tuxfamily.org/guile-lint/
.. _Elm:
   http://elm-lang.org/blog/compiler-errors-for-humans
.. _boxes:
   http://hackage.haskell.org/package/boxes
.. _vty-ui:
   http://hackage.haskell.org/package/vty-ui
.. _brick:
   http://hackage.haskell.org/package/brick
.. _Profile-Guided Static Typing for Dynamic Scripting Languages:
   http://www.cs.umd.edu/projects/PL/druby/papers/druby-tr-4935.pdf
.. _Haskell:
   http://haskell.org
.. _Typed Racket:
   http://docs.racket-lang.org/ts-guide/index.html
.. _Typed Clojure:
   http://github.com/clojure/core.typed
.. _SML:
   http://sml-family.org
.. _OCaml:
   http://caml.inria.fr/pub/docs/manual-ocaml/
.. _Hermit:
   http://hackage.haskell.org/package/hermit

Misc
~~~~

- Relevant papers:

  - `Strong Static Type Checking for Functional Common Lisp`_

- SMTLib2 example:

  .. code:: scheme

      (set-option :produce-unsat-cores true)
      (declare-const a Int)
      (declare-const b Int)
      (assert (! (> a 10) :named greater))
      (assert (! (< a 10) :named lesser))
      (assert (! (= b 5) :named lol))
      (check-sat)
      (get-info :all-statistics)
      (get-unsat-core)

.. _Strong Static Type Checking for Functional Common Lisp:
   http://www.cs.utexas.edu/users/boyer/ftp/diss/akers.pdf



.. Miscellaneous leftovers

.. _compdata:
   http://hackage.haskell.org/package/compdata
.. _typeclass-impl:
   http://okmij.org/ftp/Computation/typeclass.html
