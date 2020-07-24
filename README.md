# mgt
[![Build Status](https://travis-ci.com/mgree/mgt.svg?branch=main)](https://travis-ci.com/mgree/mgt)

Implementation of "Migrating Gradual Types" by Campora, Chen, Erwig, and Walkingshaw ([POPL 2018](https://dl.acm.org/doi/10.1145/3158103), [author PDF](http://web.engr.oregonstate.edu/~walkiner/papers/popl18-migrating-gradual-types.pdf)).

Closely follows the formalism, where the [paper-formalism](https://github.com/mgree/mgt/releases/tag/paper-formalism) tag is closest to the paper. There are several additions and changes:

  - Some tiny bug fixes and divergences from the paper.
  - Mostly imperative implementation of constraint generation and unification.
  - Constraint generation takes a term optionally annotated with gradual types and returns a term fully annotated with migrational types.
  
## TODO

- Other language features
  + [ ] Parser improvements (multi-argument lambdas, arguments in lets and letrecs)
  + [ ] Operations on constants
  + [ ] Overloading resolution
  + [ ] Let polymorphism and type schemes (need to separate unification variables and true type variables)

## QUESTIONS

- Conditionals as LUB? Otherwise, which programs get rejected?
- Left over choices, e.g., `\x:?. x : d0<?, 'a> -> d0<?, 'a>`