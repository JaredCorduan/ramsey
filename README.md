# Ramsey theory :art:

This is a work-in-progress formalization of Ramsey Theory in
[Lean](https://leanprover.github.io/).

## Constructive Proofs

### Pigeon Hole Principle

Constructive versions of Ramsey's Theorem are studied in 
> Wim Veldman and Marc Bezem, Ramsey's Theorem and the Pigeon Hole
> Principle in intuitionistic mathematics, Journal of the London
> Mathematical Society (2), Vol. 47, April 1993, pp. 193-211.

More specifically, they define a property of subsets of ℕ which
is classically equivalent to being cofinite, which they call *almost full*,
and prove that the intersection of almost full sets is almost full.

The constructive version of the infinite pidgeon hole principle was
[proved in coq](https://github.com/coq-contribs/ramsey).
An adaptation of this proof is given in `src/constructive/pigeon.lean`.

## Classical Proofs

### Pigeon Hole Principle

In `src/classical/pigeon.lean` it is shown that a subset A of ℕ is 
cofinite if and only if it is almost full.
The usual pigeon hole principle is then proved by way of the
constructive version.
