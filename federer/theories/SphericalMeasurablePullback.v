(** Federer (1969), 3.2.48, p. 284: the sets X=Phi
    inverse(A) and Y=Phi inverse(B) retain completed Hausdorff
    measurability. The preceding 3.2.47 supplies null transport;
    a true Borel hull of an already measurable set has null excess. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage
  SphericalOrthogonalPullback SphericalOrthogonalMeasureRectifiablePullback
  SphericalOrthogonalPreimageBorel RectifiableBorelHullInside RectifiableSetUP
  MeasureRectifiableSubset HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureHull HullSetAgreementConsequences
  MeasurableAlmostModification BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_measurable_measure_rectifiable_pullback]:
    completed measurability and finite rectifiability of the actual
    preimage in 3.2.48, p. 284. No Borel restriction
    is imposed on original E. The null hull difference is
    justified by E measurability, not just equal outer masses. *)
Theorem spherical_measurable_measure_rectifiable_pullback (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) E ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E) /\
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E).
Proof.
move=>hc hES hRect hMeas.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose beta:=@hausdorff_measure R X r.
pose rho:=@hausdorff_measure R Y (r+n*(n-1)%/2)%N.
have hBeta:=@hausdorff_measure_is_measure R X r.
have hRho:=@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N.
have hSphereBorel:@borel_set X (@euclidean_unit_sphere_set R n.+1).
  exact (closed_borel_set (compact_closed (@metric_hausdorff R X)
    (@euclidean_unit_sphere_compact R n.+1))).
have [M [hMB [hHull [hMRect hMS]]]]:=
  @rectifiable_borel_measure_hull_inside R n.+1 r E (@euclidean_unit_sphere_set R n.+1)
    hRect hSphereBorel hES.
have hEM:E `<=` M:=@measure_hull_subset R X beta E M hHull.
have hPreM:=@spherical_orthogonal_measure_rectifiable_pullback R n c M r hc hMS hMRect hMB.
have hPreSubset:spherical_orthogonal_preimage c E `<=` spherical_orthogonal_preimage c M.
  move=>g [hg hE]; exact (conj hg (hEM _ hE)).
split; first exact (@measure_rectifiable_subset R Y rho _ _ _ hPreSubset hPreM).
have hNull:beta (M `\` E)=0%E.
  exact (@measurable_hull_remainder_null R X beta E M hBeta hHull hMeas).
have hDiffSphere:M `\` E `<=` @euclidean_unit_sphere_set R n.+1.
  move=>x hx; exact (hMS x hx.1).
have hPreNull:=@federer_3_2_47_2 R n c (M `\` E) r hc hDiffSphere hNull.
have hPreMB:@borel_set Y (spherical_orthogonal_preimage c M).
  exact (@spherical_orthogonal_preimage_borel R n.+1 c M hMB).
apply:(@measurable_set_null_modification R Y rho hRho
  (spherical_orthogonal_preimage c M) (spherical_orthogonal_preimage c E)
  (spherical_orthogonal_preimage c (M `\` E)) hPreNull _
  (borel_regular_borel_measurable hRho (@hausdorff_measure_borel_regular R Y _) hPreMB)).
move=>g hNot; split.
- move=>[hg hM]; split; first exact hg.
  apply:contrapT=>hNotE; exact (hNot (conj hg (conj hM hNotE))).
- exact (hPreSubset g).
Qed.
