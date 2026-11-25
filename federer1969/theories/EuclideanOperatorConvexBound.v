(** Federer (1969), 4.1.9, p. 364: the original
    affine spatial differential has operator norm at
    most the corresponding convex combination of the
    endpoint operator norms. This supporting estimate
    applies the preceding least-bound norm laws of 1.7.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerNormInequalities
  OperatorNormUP OperatorNormLaws OperatorNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section EuclideanOperatorConvexBound.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation BX := (@euclidean_inner_product R m).
Local Notation BY := (@euclidean_inner_product R n).
Local Notation hBX := (@euclidean_inner_productP R m).
Local Notation hBY := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hBY).
Local Notation Op F := (@OperatorNorm.value R X Y BX BY hBX hBY m
  (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear F)).
Local Notation Law F := (@OperatorNorm.laws R X Y BX BY hBX hBY m
  (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear F)).

(** Source for [euclidean_operator_convex_bound]: the exact
    original norm of (1-t)F+tG is at most
    (1-t)||F||+t||G|| for 0<=t<=1, supporting the
    first affine mass estimate in Federer 4.1.9, p. 364.
    Zero-dimensional source and target spaces are included. *)
Theorem euclidean_operator_convex_bound (F G:Hom X Y) t:
  0<=t<=1->Op ((1-t)*:F+t*:G)<= (1-t)*Op F+t*Op G.
Proof.
move=>/andP[ht0 ht1].
have hComplement:0<=1-t by rewrite subr_ge0.
apply:(@operator_norm_le_unit R X Y BX BY hBX hBY
  (hom_as_linear ((1-t)*:F+t*:G)) _ (Law ((1-t)*:F+t*:G)) _).2=>x hx.
change (N ((1-t)*:F x+t*:G x)<=(1-t)*Op F+t*Op G).
apply:(le_trans (inner_norm_triangle hBY ((1-t)*:F x) (t*:G x))).
rewrite !inner_normZ (ger0_norm hComplement) (ger0_norm ht0).
exact:(lerD (ler_wpM2l hComplement (operator_norm_unit_bound (Law F) hx))
  (ler_wpM2l ht0 (operator_norm_unit_bound (Law G) hx))).
Qed.

(** Source for [euclidean_operator_convex_power_bound]: the
    j-th power preserves the original nonnegative operator
    norm bound, supporting Federer 4.1.9, p. 364.
    Degree zero and both zero endpoint norms are retained. *)
Theorem euclidean_operator_convex_power_bound (F G:Hom X Y) t j:
  0<=t<=1->(Op ((1-t)*:F+t*:G))^+j<=((1-t)*Op F+t*Op G)^+j.
Proof.
move=>ht.
have hT:0<=t:=(andP ht).1.
have hComplement:0<=1-t by rewrite subr_ge0;exact:(andP ht).2.
apply:lerXn2r;first exact:operator_norm_nonnegative (Law ((1-t)*:F+t*:G)).
- exact:addr_ge0 (mulr_ge0 hComplement (operator_norm_nonnegative (Law F)))
    (mulr_ge0 hT (operator_norm_nonnegative (Law G))).
- exact:euclidean_operator_convex_bound ht.
Qed.
End EuclideanOperatorConvexBound.
