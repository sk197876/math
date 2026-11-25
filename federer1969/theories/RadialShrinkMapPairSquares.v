(** Federer (1969), 4.1.15, p. 372: both displayed
    squared-distance identities for the radial shrink map.
    Reuse the original inner-product expansion from 1.7.1
    and 2.10.43 rather than introducing coordinate sums. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals ring lra.
From Federer Require Import Bilinear InnerProductUP InnerNorm
  InnerNormInequalities InnerWeightedVariance HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct RadialShrinkMapUP
  RadialShrinkMapNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section RadialShrinkMapPairSquares.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hB).
Variable r : R.
Hypothesis hr : 0 < r.
Variable P : X -> X.
Hypothesis hP : is_radial_shrink_map r P.

(** Source for [radial_shrink_outer_pair_square]: the first
    displayed identity in the proof of Lip(Psi_r)<= 1,
    Federer 4.1.15, p. 372, for |a|,|b|>=r. *)
Theorem radial_shrink_outer_pair_square a b :
  r<=N a -> r<=N b ->
  (N (P a-P b))^+2=(r-N a)^+2+(r-N b)^+2-
    2*(1-r/N a)*(1-r/N b)*B a b.
Proof.
move=> ha hb.
rewrite (inner_difference_norm_square hB)
  (radial_shrink_outer_norm hr hP ha)
  (radial_shrink_outer_norm hr hP hb)
  (radial_shrink_outer hP ha) (radial_shrink_outer hP hb)
  (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
change ((N a-r)^+2+(N b-r)^+2-
  2*((1-r/N a)*((1-r/N b)*B a b))=
  (r-N a)^+2+(r-N b)^+2-2*(1-r/N a)*(1-r/N b)*B a b).
ring.
Qed.

(** Source for [radial_shrink_outer_pair_difference_expanded]:
    the middle displayed equality on p. 372 in 4.1.15.
    The inner product is that of a/|a| and b/|b|. *)
Theorem radial_shrink_outer_pair_difference_expanded a b :
  r<=N a -> r<=N b ->
  (N (P a-P b))^+2-(N (a-b))^+2=
    2*r^+2-2*r*N a-2*r*N b-
      2*(r^+2-r*N a-r*N b)*B ((N a)^-1*:a) ((N b)^-1*:b).
Proof.
move=> ha hb.
have hA : N a!=0 := lt0r_neq0 (lt_le_trans hr ha).
have hBNonzero : N b!=0 := lt0r_neq0 (lt_le_trans hr hb).
rewrite (radial_shrink_outer_pair_square ha hb)
  (inner_difference_norm_square hB)
  (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
change (((r-N a)^+2+(r-N b)^+2-
    2*(1-r/N a)*(1-r/N b)*B a b)-
    ((N a)^+2+(N b)^+2-2*B a b)=
  2*r^+2-2*r*N a-2*r*N b-
    2*(r^+2-r*N a-r*N b)*((N a)^-1*((N b)^-1*B a b))).
field.
by apply/andP; split.
Qed.

(** Source for [radial_shrink_outer_pair_difference_factored]:
    the final displayed equality before the nonpositive sign
    in Federer 4.1.15, p. 372. *)
Theorem radial_shrink_outer_pair_difference_factored a b :
  r<=N a -> r<=N b ->
  (N (P a-P b))^+2-(N (a-b))^+2=
    2*r*(r-N a-N b)*(1-B ((N a)^-1*:a) ((N b)^-1*:b)).
Proof.
move=> ha hb.
rewrite (radial_shrink_outer_pair_difference_expanded ha hb).
ring.
Qed.

(** Source for [radial_shrink_outer_pair_difference_nonpositive]:
    the nonpositive sign at the end of the displayed
    calculation in 4.1.15, p. 372. Cauchy's inequality
    is the previously proved 1.7.1. *)
Theorem radial_shrink_outer_pair_difference_nonpositive a b :
  r<=N a -> r<=N b ->
  (N (P a-P b))^+2-(N (a-b))^+2<=0.
Proof.
move=> ha hb.
have hAPos : 0<N a := lt_le_trans hr ha.
have hBPos : 0<N b := lt_le_trans hr hb.
have hAInverse:0<=(N a)^-1 by rewrite invr_ge0;exact:ltW hAPos.
have hBInverse:0<=(N b)^-1 by rewrite invr_ge0;exact:ltW hBPos.
have hAUnit : N ((N a)^-1*:a)= 1.
  rewrite inner_normZ (ger0_norm hAInverse).
  by rewrite mulVf ?gt_eqF.
have hBUnit : N ((N b)^-1*:b)= 1.
  rewrite inner_normZ (ger0_norm hBInverse).
  by rewrite mulVf ?gt_eqF.
have hCauchy := inner_cauchy_upper hB ((N a)^-1*:a) ((N b)^-1*:b).
rewrite hAUnit hBUnit mul1r in hCauchy.
have hAngular : 0<= 1-B ((N a)^-1*:a) ((N b)^-1*:b) by lra.
have hRadial : r-N a-N b<=0 by lra.
rewrite (radial_shrink_outer_pair_difference_factored ha hb).
apply:mulr_le0_ge0; last exact:hAngular.
apply:mulr_ge0_le0; last exact:hRadial.
exact:mulr_ge0 (ler0n R 2%N) (ltW hr).
Qed.
End RadialShrinkMapPairSquares.
