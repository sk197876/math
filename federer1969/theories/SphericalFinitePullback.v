(** Federer (1969), 3.2.48, p. 284: finite Hausdorff
    rectifiability of X=Phi inverse(A), derived from the actual
    preceding-section laws. True Borel hulls preserve arbitrary original
    A; no null difference is required for this finite-mass assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage
  SphericalOrthogonalMeasureRectifiablePullback RectifiableBorelHullInside RectifiableSetUP
  MeasureRectifiableSubset HausdorffMeasure MeasureHull TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_finite_rectifiable_pullback]: the
    first rectifiability assertion for X in 3.2.48,
    p. 284. It also applies without original A measurability,
    using a genuine finite Borel hull inside the sphere and
    hereditary finite rectifiability. *)
Theorem spherical_finite_rectifiable_pullback (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E).
Proof.
move=>hc hES hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose beta:=@hausdorff_measure R X r.
pose rho:=@hausdorff_measure R Y (r+n*(n-1)%/2)%N.
have hSphereBorel:@borel_set X (@euclidean_unit_sphere_set R n.+1).
  exact (closed_borel_set (compact_closed (@metric_hausdorff R X)
    (@euclidean_unit_sphere_compact R n.+1))).
have [M [hMB [hHull [hMRect hMS]]]]:=
  @rectifiable_borel_measure_hull_inside R n.+1 r E (@euclidean_unit_sphere_set R n.+1)
    hRect hSphereBorel hES.
have hPreM:=@spherical_orthogonal_measure_rectifiable_pullback R n c M r hc hMS hMRect hMB.
apply:(@measure_rectifiable_subset R Y rho _ _ _ _ hPreM).
move=>g [hg hE]; split; first exact hg.
exact (@measure_hull_subset R X beta E M hHull (g c) hE).
Qed.
