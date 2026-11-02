(** Federer (1969), 1.7.2, p. 28: existence of the dual inner product. This
    construction is used only by the sealing module; downstream proofs use
    the specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerPolarity
  LinearBasis AlternatingCoordinates TensorUP Bilinear.
From Federer Require Import InnerDualUP InnerPolaritySurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DualConstruction.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation F := (A_m V R^o 1).
Local Notation beta := (inner_polarity hB).
Let hs := @inner_polarity_surjective R V B hB n e he.
Let hi := @inner_polarity_injective R V B hB.
Let g := linear_inverse hi hs.

(** Source for [dual_inner_product_witness]: Federer 1.7.2,
    p. 28, supporting existence witness: transfer the inner product
    along the inverse of the polarity isomorphism. *)
Definition dual_inner_product_witness (a b : F) := B (g a) (g b).

(** Source for [dual_inner_product_witnessP]: Federer 1.7.2,
    p. 28, the transferred function satisfies the abstract dual
    inner-product specification. *)
Theorem dual_inner_product_witnessP :
  is_dual_inner_product hB dual_inner_product_witness.
Proof.
constructor.
- constructor.
  + split=> y a x z; rewrite /dual_inner_product_witness.
    * rewrite /g linearP (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
      by [].
    * rewrite /g linearP (bilDr (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
      by [].
  + by move=> a b; rewrite /dual_inner_product_witness (inner_symmetric hB).
  + move=> a; rewrite /dual_inner_product_witness (inner_positive hB).
    have hg : injective g by apply: can_inj; exact: linear_inverseK.
    by rewrite -(linear0 g) (inj_eq hg).
- move=> x y; by rewrite /dual_inner_product_witness /g !linear_inverseKV.
Qed.
End DualConstruction.
