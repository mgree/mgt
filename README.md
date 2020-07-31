# mgt
[![Build Status](https://travis-ci.com/mgree/mgt.svg?branch=main)](https://travis-ci.com/mgree/mgt)

Implementation of "Migrating Gradual Types" by Campora, Chen, Erwig, and Walkingshaw ([POPL 2018](https://dl.acm.org/doi/10.1145/3158103), [author PDF](http://web.engr.oregonstate.edu/~walkiner/papers/popl18-migrating-gradual-types.pdf)).

Closely follows the formalism, where the [paper-formalism](https://github.com/mgree/mgt/releases/tag/paper-formalism) tag is closest to the paper. There are several additions and changes:

  - Some tiny bug fixes and divergences from the paper.
  - Mostly imperative implementation of constraint generation and unification.
  - Constraint generation takes a term optionally annotated with gradual types and returns a term fully annotated with migrational types.
  - Operator overloading.

## Overloading

Consider a source operation like `==` in JS:

```
true == true
1    == 1
0    == false
```

Each of these returns `true`. In the target language, there are really three
underlying operations:

```
==b : bool -> bool -> bool
==i : int  -> int  -> bool
==? : ?    -> ?    -> bool
```

Any use of `==` in the source language ought to turn into one of these
three operators. But which one? If you know the argument types and they
fit, you should prefer `==b` and `==i`. The rest of the time, it's gotta
be `==?`.

The situation is even worse for something like `+`, where you have in
the target language:

```
+i : int    -> int    -> int
+s : string -> string -> string
+? : ?      -> ?      -> ?
```

(Recalling that `5 +? hi` is `"5hi"` and `true +? "love"` is `"truelove"`, just
for lols.) Type inference itself depends on overloading resolution.

### Current algorithm

Only `==` and `+` (with addition `+i` and string concatenation `+s`) are handled
right now. There are two new ingredients:

  1. Biased choice. You can specify that you'd prefer a given choice to be made
     if possible. When computing valid eliminators, biased choice will keep the
     biased side and ignore the unbiased one---so long as there's a solution.
  2. Ground constraints. You can require that a type _really_ be of some
     particular ground type. For now, that's just base types, but it should be
     possible to extend this.

Taken together, an overloaded operation uses biased choice to try to select
concrete implementations, but the arguments are given ground constraints so that
we don't over-narrow things.

Some examples (in `eg/`) clarify things well. In particular:

```
let eq = \x:?. \y:?. x == y in 
eq 5 true
```

Will infer `x:int` and `y:bool`, but correctly select `==?`. Inference
generalizes correctly:

```
let eq = \x:?. \y:?. x == y in 
eq 5 true && eq 0 0 && eq false false
```

Will infer `x:?` and `y:?` and select `==?`.

Critically, writing `0 == 0 && true == false` will correctly select `==i` and
`==b`, respectively.

## Assumptions/holes

The `assume x [: t] in e` form lets you add bindings at arbitrary types without
definitions. It uses typed holes `__[name]` generate fresh type variables.

It's tempting to have a typed hole have type `?`, but that doesn't work like
other bits of the inference. If you want something to be `?`, write `assume foo
: ? in bar`. Writing `assume foo in bar` will try to infer `foo`'s type.

## TODO

- Other language features
  + Ensure that choices don't show up in the final, eliminated AST
    - [ ] Using tests, or...
    - [ ] `eliminate` operation that changes types to really have no choice left
          (would need more than one `Expr`, trait)
  + [ ] Let polymorphism and type schemes (need to separate unification
        variables and true type variables). First cut: just have `Ctx` track
        type schemes, instantiating at every variable. Most things will be
        monomorphic, but assumes can give us polymorphism. Operation resolution
        may need to yield type schemes rather than types, too

- [ ] Implement Rastogi et al.'s "The Ins and Outs of Gradual Type Inference".

- [ ] Herder-style scoring?

- [ ] Interpreter

- [ ] Dynamizer (from `SourceExpr`)

- [ ] Understand top-level weirdness. `if true then (true : ?) else (0 : ?)`
      will type check just fine in both lax and strict regimes.  Coercion
      insertion will tag both branches as bool, but the migrational inference
      says the whole thing has either type bool or int, depending. At present,
      this crashes on an assertion in main. If you put it in a context, e.g.,
      `false && ...`, then the right coercions will be generated and everything
      is fine.

      Annotating one branch seems to work fine. It seems like you could keep 
      more information in an if about which return type you'd like it to be.
      Simply putting in annotations doens't quite cut it, because elimination
      will leave one side ill-typed: in the migration where the whole 
      conditional has type `int`, the `true : int` annotation you get will break
      things.

      It's a bad situation. On the one hand, coercion insertion doesn't give you
      the exact inferred type. On the other hand, the inferred type sucks!

# Acknowledgments

Conversations with [Arjun Guha](https://twitter.com/arjunguha), [Colin
Gordon](https://twitter.com/csgordon/), [Ron
Garcia](https://twitter.com/rg9119), and [Jens
Palsberg](http://web.cs.ucla.edu/~palsberg/) were helpful.
[@jorendorff](https://twitter.com/jorendorff) gave a tip on concrete syntax.
  
