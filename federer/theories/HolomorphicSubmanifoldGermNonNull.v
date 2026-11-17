(** Federer (1969), 3.4.12, p. 339, extending
    3.4.8(13), p. 335: a nonempty complex m-manifold
    germ has positive real H^(2m) mass in every containing
    representative. Apply the existing real nonnullity theorem through
    the original paired real coordinates and exact germ inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness StandardHermitianCoordinates
  HolomorphicCoordinateNorm ComplexEuclideanCoordinates ComplexEuclideanCoordinateTopology
  HolomorphicSubmanifoldUP HolomorphicSubmanifoldRealCoordinates SetGermUP SetGermLaws SetGermOrder SetGermBoundary
  SetGermInversePreimageOrder SubmanifoldGermNonNull HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nonnull.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Y:=(R_n R (n+n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation TX:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
(** Source for [holomorphic_submanifold_germ_nonnull]: the actual
    positive mass at doubled real dimension in 3.4.12,
    p. 339, applied to the dimension comparison of
    3.4.8(13), p. 335. The manifold need not contain
    the germ centre, and the containing set need not be measurable. *)
Theorem holomorphic_submanifold_germ_nonnull (Z S:set X):
  @is_holomorphic_submanifold R X NX hNX m Z ->
  @set_germ TX 0 Z<>@set_germ TX 0 set0 ->
  set_germ_subset (@set_germ TX 0 Z) (@set_germ TX 0 S) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+n))) (m+m)
    ((@complex_from_real_coordinate_hom R n) @^-1` S)<>0%E.
Proof.
move=>hZ hNonempty hContained.
pose u:=@complex_real_coordinate_hom R n.
pose v:=@complex_from_real_coordinate_hom R n.
have hU:=@complex_real_coordinate_hom_continuous R n.
have hV:=@complex_from_real_coordinate_hom_continuous R n.
have hU0:u 0 = 0 by rewrite /u linear0.
have hV0:v 0 = 0 by rewrite /v linear0.
have hUV:cancel u v:=@complex_real_coordinatesK R n.
have hPreNonempty:@set_germ TY 0 (v @^-1` Z)<>@set_germ TY 0 set0.
  move=>hEmpty;apply:hNonempty;apply:set_germ_subset_empty.
  apply:(@set_germ_inverse_preimage_subset_reflect TY TX v u 0 0 Z set0 hU hU0 hUV).
  rewrite preimage_set0 hEmpty;exact:set_germ_subset_reflexive.
have hPreContained:=@set_germ_continuous_preimage_subset TY TX v 0 0 Z S hV hV0 hContained.
exact:(@analytic_submanifold_germ_nonnull R (n+n) (m+m) (v @^-1` Z) (v @^-1` S)
  (holomorphic_submanifold_paired_real_coordinates hZ) hPreNonempty hPreContained).
Qed.
End Nonnull.
