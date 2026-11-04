(** Federer (1969), 3.2.46, p. 281: a local positive symmetric
    factor is an automorphism. Its inverse has a finite homogeneous
    bound, permitting the local comparison radius to be expressed in
    L-coordinates. The inverse is a local proof witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates InnerProductUP InnerNorm OperatorNorm
  EuclideanLinearMaps PositiveSymmetricNormFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_norm_factor_inverse_bound]: the local
    change L in Federer 3.2.46, p. 281, controls ordinary norms in
    both directions. This is the inverse-direction bound, derived
    from its proved automorphism law and 1.7.6, pp. 33--34. *)
Lemma positive_norm_factor_inverse_bound (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n}) :
  is_positive_symmetric_norm_factor hB L -> exists K : R,
    0 < K /\ forall v,
      inner_norm (@euclidean_inner_productP R n) v <=
        K * inner_norm (@euclidean_inner_productP R n) (L v).
Proof.
move=> hL.
have [M [hLM hML]] := euclidean_linear_inverse (positive_norm_factor_injective hL).
pose hE := @euclidean_inner_productP R n.
pose c := linear_operator_norm hE hE (@coordinate_basisP R n) M.
have hc : 0 <= c := linear_operator_norm_nonnegative hE hE (@coordinate_basisP R n) M.
exists (c+1); split; first by lra.
move=> v.
have h := linear_operator_norm_bound hE hE (@coordinate_basisP R n) M (L v).
rewrite hLM in h.
apply: le_trans h _; apply: ler_wpM2r; first exact: inner_norm_nonnegative.
by rewrite lerDl ler01.
Qed.
