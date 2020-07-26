# mgt
[![Build Status](https://travis-ci.com/mgree/mgt.svg?branch=main)](https://travis-ci.com/mgree/mgt)

Implementation of "Migrating Gradual Types" by Campora, Chen, Erwig, and Walkingshaw ([POPL 2018](https://dl.acm.org/doi/10.1145/3158103), [author PDF](http://web.engr.oregonstate.edu/~walkiner/papers/popl18-migrating-gradual-types.pdf)).

Closely follows the formalism, where the [paper-formalism](https://github.com/mgree/mgt/releases/tag/paper-formalism) tag is closest to the paper. There are several additions and changes:

  - Some tiny bug fixes and divergences from the paper.
  - Mostly imperative implementation of constraint generation and unification.
  - Constraint generation takes a term optionally annotated with gradual types and returns a term fully annotated with migrational types.
  
## TODO

- Other language features
  + [ ] Parser improvements (multi-argument lambdas, arguments in lets and letrecs, assume expressions (let w/o defn))
  + [ ] Operations on constants with overloading
        Mostly done. Not sure how to handle `==?` always remaining as an option...

        Correct solution: ad hoc the overloaded ones for now.
        
        testing: add asserts to ensure that choices don't show up in the final, eliminated AST
  + [ ] Let polymorphism and type schemes (need to separate unification variables and true type variables). First cut: just have `Ctx` track type schemes, instantiating at every variable. Most things will be monomorphic, but assumes can give us polymorphism.

        operation resolution may need to yield type schemes rather than types, too
  + [ ] `eliminate` operation that changes types to really have no choice left (would need more than one `Expr`...)