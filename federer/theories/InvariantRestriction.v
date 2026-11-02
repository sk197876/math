(** Federer (1969), 1.7.3, p. 29: restrictions to invariant subspaces in the
    orthogonal reduction argument. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier
  InnerProductUP InnerProductRestriction SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Restriction.
Variable R : realFieldType.
Variable V : lmodType R.
Variable f : {linear V -> V}.
Variable W : subspace V.
Hypothesis hW : invariant_subspace f W.

(** Source for [invariant_restriction]: Federer 1.7.3, p. 29,
    supporting definition: the endomorphism induced on an invariant
    subspace has the same values as the original map. *)
Definition invariant_restriction (x : subspace_space W) : subspace_space W :=
  subspace_lift (hW (subspace_valP x)).

(** Source for [invariant_restrictionE]: Federer 1.7.3, p. 29,
    supporting compatibility of restriction with inclusion. *)
Lemma invariant_restrictionE x :
  subspace_val (invariant_restriction x) = f (subspace_val x).
Proof. by []. Qed.

(** Source for [invariant_restriction_linear]: Federer 1.7.3,
    p. 29, supporting linearity of the restricted endomorphism. *)
Lemma invariant_restriction_linear : linear invariant_restriction.
Proof.
move=> a x y; apply: subspace_val_injective.
by rewrite !linearP invariant_restrictionE linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R
  (subspace_space W) (subspace_space W) *:%R
  invariant_restriction invariant_restriction_linear.

Variable B : V -> V -> R.

(** Source for [symmetric_invariant_restriction]: Federer 1.7.3, p. 29,
    supporting restriction of a symmetric map to an invariant subspace *)
Lemma symmetric_invariant_restriction : is_symmetric_endomorphism B f ->
  is_symmetric_endomorphism (@restricted_inner_product R V B W) invariant_restriction.
Proof. by move=> hf x y; exact: hf. Qed.

(** Source for [skewsymmetric_invariant_restriction]: Federer 1.7.3, p. 29,
    supporting restriction of a skewsymmetric map to an invariant subspace *)
Lemma skewsymmetric_invariant_restriction : is_skewsymmetric_endomorphism B f ->
  is_skewsymmetric_endomorphism (@restricted_inner_product R V B W) invariant_restriction.
Proof. by move=> hf x y; exact: hf. Qed.
End Restriction.
