(** Federer 2.10.2(1), p. 171: uniform length-to-cost comparison for
    open generators at the circle diameter cutoff. Independent scalar
    constants, actual cap projection and actual antipodal disjointness
    are combined; no measure comparison is assumed in the constants. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume
  PlanarUnitCircleGeometry PlanarCircleSmallCapMass PlanarCircleOpenHalfMass
  PlanarCircleCutoffConstants HausdorffMeasure MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [planar_circle_open_generator_length_bound]: Federer
    2.10.2(1), p. 171, supporting every actual open covering generator.
    The original generator may miss the circle or be empty. Its finite
    diameter is derived from the cutoff, not an additional premise. *)
Theorem planar_circle_open_generator_length_bound (R:realType)
    (delta radius coeff:R)
    (hc:is_planar_circle_cutoff_constants (euclidean_unit_ball_volume R 2)
      delta radius coeff)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))):
  open S -> extended_metric_diameter S <= (2:R)%:E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@planar_unit_circle R `&` S) <= coeff%:E*extended_metric_diameter S.
Proof.
move=>hOpen hDiam.
have [/andP[hd hHalf] [hIA [hr1 [hr2 [hInvCoeff [hRatioCoeff hCoeff]]]]]]:=hc.
have hHalfOne:(1/2<=1:>R)%R by clear -R; lra.
have hd1:(delta<=1)%R:=le_trans (ltW hHalf) hHalfOne.
have hr:(0<radius)%R:=lt_trans ltr01 hr1.
have hAlpha:(0<euclidean_unit_ball_volume R 2)%R:=(euclidean_unit_ball_volumeE R 2).2.
have hRadiusSquare:(radius^+2<=2-2*delta)%R by rewrite hr2.
have hNonneg:=metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hCut:=hDiam.
case he:(extended_metric_diameter S) hNonneg hDiam=>[d| |] hNonneg hDiam; last 2 first.
- by rewrite leye_eq in hDiam.
- by [].
have hd0:(0<=d)%R by move:hNonneg; rewrite lee_fin.
case:(leP d radius)=>hCase.
- have hSmallCut:extended_metric_diameter S<=radius%:E by rewrite he lee_fin.
  have hSmall:=@small_planar_circle_intersection_length R S delta radius hd hd1
    (ltW hr) hRadiusSquare hSmallCut.
  rewrite he -EFinM in hSmall.
  apply:le_trans hSmall _; rewrite -EFinM lee_fin.
  have hMono:=ler_wpM2r hd0 hInvCoeff.
  exact:hMono.
- have hHalfMass:=@open_planar_circle_intersection_half_length R S hOpen hCut.
  apply:le_trans hHalfMass _; rewrite -EFinM lee_fin.
  have hRatio0:(0<=euclidean_unit_ball_volume R 2/radius)%R by rewrite divr_ge0 // ltW.
  have hBound:=ler_wpM2l hRatio0 (ltW hCase).
  rewrite divfK ?gt_eqF // in hBound.
  exact:le_trans hBound (ler_wpM2r hd0 hRatioCoeff).
Qed.
