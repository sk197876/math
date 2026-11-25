(** Supporting finite-dimensional linear algebra for Federer (1969), 1.6.3,
    p. 25, intersection corollary. This file relates the project's abstract
    basis predicate to the finite-dimensional vector-space structure already
    used for dimensions. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SubspaceBasisProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spanning_dimension_independent]: Federer 1.6.3,
    p. 25, dimension argument in the intersection corollary. Supporting
    fact: a spanning family whose length equals the dimension is
    independent. The dimension is specified by an arbitrary basis. *)
Theorem spanning_dimension_independent (K : fieldType) (V : lmodType K)
  n (b : 'I_n -> V) (hb : is_basis b) (e : 'I_n -> V) :
  (forall v, in_finite_span e v) -> finite_independent e.
Proof.
move=> hs; pose U := finite_basis_vect hb.
pose t : n.-tuple U := [tuple e i | i < n].
have ht (i : 'I_n) : t`_i = e i := nth_mktuple e (0 : U) i.
have hspan : (<<t>> = {:U})%VS.
  apply/vspaceP=> v; rewrite memvf; apply/idP.
  have [c ->] := hs v.
  apply: memv_suml => i _; apply: memvZ.
  apply: memv_span; apply/tnthP; exists i; by rewrite /t tnth_mktuple.
have hbase : basis_of {:U} t.
  by rewrite basisEdim hspan subvv size_tuple dimvf /U finite_basis_dimension card_ord leqnn.
have /freeP hi := basis_free hbase.
move=> c hc i; apply: hi.
have heq : (\sum_j c j *: t`_j) = \sum_j c j *: e j.
  apply: eq_bigr => j _; by rewrite ht.
by rewrite heq.
Qed.

(** Source for [spanning_independent_iff_size]: Federer 1.6.3,
    p. 25, dimension argument in the intersection corollary. Supporting
    equivalence: a spanning family is independent iff its length equals
    the size of a basis. *)
Theorem spanning_independent_iff_size (K : fieldType) (V : lmodType K)
  n (b : 'I_n -> V) (hb : is_basis b) m (e : 'I_m -> V) :
  (forall v, in_finite_span e v) -> (finite_independent e <-> m = n).
Proof.
move=> hs; split.
- move=> hi; exact: finite_basis_size (finite_basis_criterion hi hs) hb.
- move=> h; subst m; exact: (@spanning_dimension_independent K V n b hb e hs).
Qed.

(** Source for [subspace_family_spans]: Federer 1.6.3, p. 25,
    dimensions of sums of annihilators. Supporting transfer: a family
    spanning S in the ambient space also spans the carrier of S. *)
Lemma subspace_family_spans (K : fieldType) (V : lmodType K)
  (S : subspace V) n (e : 'I_n -> V) (hS : forall i, S (e i)) :
  (forall v, S v -> in_finite_span e v) ->
  forall v : subspace_space S, in_finite_span (subspace_family hS) v.
Proof.
move=> hs v; have [c hc] := hs _ (subspace_valP v).
exists c; apply: val_inj.
change (subspace_val v = subspace_val (\sum_i c i *: subspace_family hS i)).
rewrite linear_sum; under eq_bigr do rewrite linearZ.
exact: hc.
Qed.
