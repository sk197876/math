(** Federer (1969), 3.3.19, pp. 302–304:
    elementary two-coordinate norm bound supporting the
    actual circular and convex-boundary parametrizations. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric PlanarCircleCapCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [planar_coordinate_norm_upper]: the
    actual Euclidean norm is at most the sum
    of the absolute original coordinates, supporting
    the boundary curve in 3.3.19, p. 304.
    This is proved from the original inner product. *)
Lemma planar_coordinate_norm_upper (R:realType) (v:R_n R 2):
  inner_norm (@euclidean_inner_productP R 2) v<=
    `|v ord0|+`|v (@Ordinal 2 1 (erefl true))|.
Proof.
have hSquare:=inner_norm_sqr (@euclidean_inner_productP R 2) v.
rewrite planar_euclidean_inner_coordinates -!expr2 in hSquare.
have h0:0<=`|v ord0| by exact:normr_ge0.
have h1:0<=`|v (@Ordinal 2 1 (erefl true))| by exact:normr_ge0.
have hNorm:=inner_norm_nonnegative (@euclidean_inner_productP R 2) v.
have hAbs0:`|v ord0|^+2=(v ord0)^+2 by rewrite real_normK ?num_real.
have hAbs1:`|v (@Ordinal 2 1 (erefl true))|^+2=(v (@Ordinal 2 1 (erefl true)))^+2.
  by rewrite real_normK ?num_real.
nra.
Qed.
