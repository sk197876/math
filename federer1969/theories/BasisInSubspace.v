(** Federer (1969), 1.6.6, p. 27: the complex factors of a nonzero paired
    vector form a basis of its associated complex subspace. Supporting
    general basis criterion for a specified subspace. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates SubspaceCarrier FiniteSpans
  FiniteSpanSpace FiniteBasisCriterion FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Basis.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.
Variable p : nat.
Variable v : 'I_p -> V.
Hypothesis hv : finite_independent v.
Hypothesis hspan : forall x, in_finite_span v x <-> S x.

(** Source for [basis_in_subspace_member]: Federer 1.6.6,
    p. 27, the factors belong to the associated plane. Supporting
    membership of an independent spanning family's vectors. *)
Lemma basis_in_subspace_member j : S (v j).
Proof. apply/hspan; exact: finite_span_generator. Qed.

(** Source for [basis_in_subspace]: Federer 1.6.6, p. 27,
    basis of the associated complex plane. The same vectors regarded
    as elements of the specified subspace. *)
Definition basis_in_subspace j := subspace_lift (basis_in_subspace_member j).

(** Source for [basis_in_subspace_independent]: Federer
    1.6.6, p. 27, basis of the complex plane. Independence is
    preserved by passing to the subspace carrier. *)
Lemma basis_in_subspace_independent : finite_independent basis_in_subspace.
Proof.
move=> c hc; apply: hv.
have h := congr1 (@subspace_val K V S) hc.
rewrite linear_sum linear0 in h.
have hs : (\sum_i subspace_val (c i *: basis_in_subspace i)) = \sum_i c i *: v i.
  apply: eq_bigr => i _; by rewrite linearZ.
by rewrite hs in h.
Qed.

(** Source for [basis_in_subspaceP]: Federer 1.6.6, p. 27,
    the factors form a basis of their associated complex plane.
    Supporting implication: an independent family whose span is S
    forms a basis of the carrier of S. *)
Theorem basis_in_subspaceP : is_basis basis_in_subspace.
Proof.
apply: finite_basis_criterion basis_in_subspace_independent _ => x.
have [c hc] := (proj2 (hspan (subspace_val x))) (subspace_valP x).
exists c; apply: val_inj.
change (subspace_val x = subspace_val (\sum_i c i *: basis_in_subspace i)).
rewrite linear_sum hc; apply: eq_bigr => i _; by rewrite linearZ.
Qed.
End Basis.
