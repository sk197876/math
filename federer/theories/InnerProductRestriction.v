(** Federer (1969), 1.7.3, p. 29: inner products on subspaces in the
    orthogonal decomposition argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm TensorUP Bilinear
  ModuleQuotient SubspaceCarrier.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Restriction.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable W : subspace V.

(** Source for [restricted_inner_product]: Federer 1.7.3,
    p. 29, supporting restriction of the ambient inner product
    to the vector space carried by a subspace. *)
Definition restricted_inner_product (x y : subspace_space W) :=
  B (subspace_val x) (subspace_val y).

(** Source for [restricted_inner_productP]: Federer 1.7.3,
    p. 29, the restricted form is an inner product, with no finite
    dimension hypothesis. *)
Theorem restricted_inner_productP : is_inner_product restricted_inner_product.
Proof.
constructor.
- split=> y a x z; rewrite /restricted_inner_product linearP.
  + by rewrite (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
  + by rewrite (bilDr (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
- by move=> x y; rewrite /restricted_inner_product (inner_symmetric hB).
- move=> x; rewrite /restricted_inner_product (inner_positive hB).
  by rewrite -(linear0 (@subspace_val R V W)) (inj_eq (@val_inj _ _ _)).
Qed.
End Restriction.
