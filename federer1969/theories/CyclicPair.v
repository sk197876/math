(** Federer (1969), 1.7.3, p. 29: the invariant span of x and f(x) when x is
    an eigenvector of f squared. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SymmetricEndomorphisms
  InvariantFiniteSpan FiniteSpans FiniteSpanSpace InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cyclic_pair_invariant]: Federer 1.7.3, p. 29,
    the span of x and f(x) is invariant if f(f(x)) is a scalar
    multiple of x. This algebraic step works over any field. *)
Lemma cyclic_pair_invariant (R : fieldType) (V : lmodType R)
    (f : {linear V -> V}) (x : V) lambda :
  f (f x) = lambda *: x ->
  invariant_subspace f
    (finite_span_subspace (ordinal_snoc (fun _ : 'I_1 => x) (f x))).
Proof.
move=> he; apply: finite_span_invariant => i.
case: (unliftP ord_max i) => [j ->|->].
- rewrite ordinal_snoc_lift; exact: in_finite_span_last.
- rewrite ordinal_snoc_last he; apply: in_finite_span_scale.
  apply: in_finite_span_snoc.
  exact (@finite_span_generator R V 1 (fun _ => x) ord0).
Qed.
