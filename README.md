# mgt
[![Build Status](https://travis-ci.com/mgree/mgt.svg?branch=main)](https://travis-ci.com/mgree/mgt)

Implementation of "Migrating Gradual Types" by Campora, Chen, Erwig, and Walkingshaw ([POPL 2018](https://dl.acm.org/doi/10.1145/3158103), [author PDF](http://web.engr.oregonstate.edu/~walkiner/papers/popl18-migrating-gradual-types.pdf)).

Closely follows the formalism, where the [paper-formalism](https://github.com/mgree/mgt/releases/tag/paper-formalism) tag is closest to the paper. There are several additions and changes:

  - Some tiny bug fixes and divergences from the paper.
  - Mostly imperative implementation of constraint generation and unification.
  - Constraint generation takes a term optionally annotated with gradual types and returns a term fully annotated with migrational types.

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

(Recalling that `5 +? hi` is `"5hi"` and `true +? "love"` is
`"truelove"`, just for lols.) Type inference itself is going to depend
on overloading resolution.

### Current algorithm

Only `==` is handled right now. Given `\x:?. \y:?. x == y`, constraint
generation yields:

```
e = \x : a0. \y : a1. x d1<d0<==?, ==b>, ==i> y
m = a0 -> a1 -> d1<d0<bool,bool>,bool>
constraints = d1<d0<? ≈⊤ a0 ⋀ ? ≈⊤ a1, bool ≈⊤ a0 ⋀ bool ≈⊤ a1>, int ≈⊤ a0 ⋀ int ≈⊤ a1>
pi = ⊤
```

This encoding only does okay. In this instance, the "you can't go wrong going
right" policy will just select `==i` when `==?` is the only safe option.

On the more interesting `let eq = \x:?. \y:?. x == y in eq 5 true` we find:

```
e = 
  let eq : d0<?,a0> -> d1<?,a1> -> d3<d2<bool,bool>,bool> = \x : d0<?,a0>. \y : d1<?,a1>. x d3<d2<==?, ==b>, ==i> y in
  ((eq 5 true) && (eq 0 0)) && (eq false false)
m = bool
constraints = d3<d2<? ≈⊤ d0<?,a0> ⋀ ? ≈⊤ d1<?,a1>,
    bool ≈⊤ d0<?,a0> ⋀ bool ≈⊤ d1<?,a1>>,
    int ≈⊤ d0<?,a0> ⋀ int ≈⊤ d1<?,a1>> ⋀ d0<?,a0>
    ≈⊤
    int ⋀ d1<?,a1> ≈⊤ bool ⋀ d0<?,a0> ≈⊤ int ⋀ d1<?,a1>
    ≈⊤
    int ⋀ bool ≈⊤ d3<d2<bool,bool>,bool> ⋀ bool
    ≈⊤
    d3<d2<bool,bool>,bool> ⋀ d0<?,a0> ≈⊤ bool ⋀ d1<?,a1>
    ≈⊤
    bool ⋀ bool ≈⊤ bool ⋀ bool ≈⊤ d3<d2<bool,bool>,bool>
```

The sole valid eliminator is `{d0.L, d1.L}`; since you can't go wrong going
right, the maximal valid eliminator is `{d3.R, d2.R, d0.L, d1.L}`, yielding:

```
let eq : ? -> ? -> bool = \x : ?. \y : ?. x ==i y in
((eq 5 true) && (eq 0 0)) && (eq false false)
: bool
```

Ack!

So far as I can tell, the core issue is that using consistency and right-leaning
leads to bad choices. Simply putting `?` on the right doesn't do the trick,
either. I think the key issue is that operator overloading shouldn't use
consistency, but equality: if you can't _prove_ that both arguments are `bool`s,
you have no business using `==b`.

## TODO

- Other language features
  + [ ] Parser improvements (multi-argument lambdas, arguments in lets and letrecs, assume expressions (let w/o defn))
  + Ensure that choices don't show up in the final, eliminated AST
    - [ ] Using tests, or...
    - [ ] `eliminate` operation that changes types to really have no choice left (would need more than one `Expr`, trait)
  + [ ] Let polymorphism and type schemes (need to separate unification variables and true type variables). First cut: just have `Ctx` track type schemes, instantiating at every variable. Most things will be monomorphic, but assumes can give us polymorphism.

        operation resolution may need to yield type schemes rather than types, too

# Acknowledgments

Conversations with [Arjun Guha](https://twitter.com/arjunguha) and [Colin
Gordon](https://twitter.com/csgordon/) were helpful.
[@jorendorff](https://twitter.com/jorendorff) gave a tip on concrete syntax.
  
