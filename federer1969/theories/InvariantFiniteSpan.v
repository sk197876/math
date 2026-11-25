(** Federer (1969), 1.7.3, p. 29: invariant spans in the one- and
    two-dimensional reduction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient FiniteSpans FiniteSpanSpace
  SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_span_subspace_contained]: Federer 1.7.3,
    p. 29, supporting containment: a subspace containing all
    generators contains every linear combination. *)
Lemma finite_span_subspace_contained (R : fieldType) (V : lmodType R)
    n (e : 'I_n -> V) (W : subspace V) :
  (forall i, W (e i)) -> forall x, in_finite_span e x -> W x.
Proof.
move=> he x [c ->]; elim/big_rec: _ => [|i v _ hv]; first exact: subspace_zero.
apply: subspace_add; last exact hv.
exact: subspace_scale (he i).
Qed.

(** Source for [finite_span_invariant]: Federer 1.7.3, p. 29,
    supporting invariance criterion: it suffices that the image
    of each generator belongs to the same finite span. *)
Lemma finite_span_invariant (R : fieldType) (V : lmodType R)
    (f : {linear V -> V}) n (e : 'I_n -> V) :
  (forall i, in_finite_span e (f (e i))) ->
  invariant_subspace f (finite_span_subspace e).
Proof.
move=> he x [c ->]; rewrite linear_sum.
under eq_bigr do rewrite linearZ.
elim/big_rec: _ => [|i v _ hv]; first exact: in_finite_span_zero.
apply: in_finite_span_add; last exact hv.
exact: in_finite_span_scale (he i).
Qed.
