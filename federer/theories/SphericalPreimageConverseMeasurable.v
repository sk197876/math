(** Federer (1969), 3.2.48, p. 284: completed
    measurability of the actual Phi preimage implies completed
    measurability of the original finite rectifiable sphere set.
    Supporting the signed fibre integrals: true finite Borel
    hulls and the proved all-set 3.2.47 mass law
    discharge the completion issue. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage
  SphericalPullbackPushforward SphericalFinitePullback SphericalOrthogonalPreimageBorel
  RectifiableSetUP RectifiableBorelHullInside MeasureRectifiableSubset
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureRestriction
  MeasurePushforward MeasureScaleIntegral MeasureHull HullSetAgreementConsequences
  MeasurableAlmostModification BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_converse_measurable]: supporting
    the original completed measurable intersection in 3.2.48,
    p. 284. A null difference is asserted only after
    the actual preimage is proved measurable; equal outer
    mass alone is never used to declare an arbitrary
    nonmeasurable hull difference null. *)
Theorem spherical_preimage_converse_measurable (R:realType) d r
    (c:R_n R d.+1) (E:set (R_n R d.+1)):
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) r E ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1)) (r+d*(d-1)%/2))
    (spherical_orthogonal_preimage c E) ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) E.
Proof.
move=>hc hES hRect hPreMeas.
pose X:=inner_metric_space (@euclidean_inner_productP R d.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1).
pose beta:=@hausdorff_measure R X r.
pose rho:=@hausdorff_measure R Y (r+d*(d-1)%/2)%N.
pose C:=spherical_preimage_mass_scale R d r.
have hC:0<C:=spherical_preimage_mass_scale_positive R d r.
have hBeta:=@hausdorff_measure_is_measure R X r.
have hRho:=@hausdorff_measure_is_measure R Y (r+d*(d-1)%/2)%N.
have hSphere:@borel_set X (@euclidean_unit_sphere_set R d.+1).
  exact (closed_borel_set (compact_closed (@metric_hausdorff R X)
    (@euclidean_unit_sphere_compact R d.+1))).
have [M [hMB [hHull [hMRect hMS]]]]:=@rectifiable_borel_measure_hull_inside R d.+1 r E
  (@euclidean_unit_sphere_set R d.+1) hRect hSphere hES.
have hEM:E `<=` M:=@measure_hull_subset R X beta E M hHull.
have hMassTarget:beta E=beta M:=measure_hull_equal_measure hBeta hHull.
have hPreE:=@spherical_finite_rectifiable_pullback R d r c E hc hES hRect.
have hPreM:=@spherical_finite_rectifiable_pullback R d r c M hc hMS hMRect.
have hPreMB:@borel_set Y (spherical_orthogonal_preimage c M):=
  spherical_orthogonal_preimage_borel c hMB.
have hPreMM:measure_measurable rho (spherical_orthogonal_preimage c M):=
  borel_regular_borel_measurable hRho (@hausdorff_measure_borel_regular R Y (r+d*(d-1)%/2)%N) hPreMB.
have hPreSubset:spherical_orthogonal_preimage c E `<=` spherical_orthogonal_preimage c M.
  move=>g [hg hE]; exact (conj hg (hEM _ hE)).
have hMass S (hSS:S `<=` @euclidean_unit_sphere_set R d.+1)
    (hSR:is_measure_m_rectifiable beta r S):
    rho (spherical_orthogonal_preimage c S)=(C%:E*beta S)%E.
  have h:=congr1 (fun nu=>nu setT) (@spherical_pullback_pushforward R d r c S hc hSS hSR).
  by rewrite /measure_pushforward preimage_setT /measure_scale /measure_restrict !setIT in h.
have hMassPre:rho (spherical_orthogonal_preimage c E)=rho (spherical_orthogonal_preimage c M).
  by rewrite (hMass E hES hRect) (hMass M hMS hMRect) hMassTarget.
have hSourceHull:=@measure_hull_of_finite_equal_measure R Y rho hRho
  (spherical_orthogonal_preimage c E) (spherical_orthogonal_preimage c M)
  hPreSubset hPreMM hMassPre hPreE.2.
have hSourceNull:=@measurable_hull_remainder_null R Y rho
  (spherical_orthogonal_preimage c E) (spherical_orthogonal_preimage c M)
  hRho hSourceHull hPreMeas.
have hDifference:spherical_orthogonal_preimage c (M `\` E)=
    spherical_orthogonal_preimage c M `\` spherical_orthogonal_preimage c E.
  apply/seteqP; split=>g.
  - move=>[hg [hm hn]]; split; first exact (conj hg hm).
    by move=>[_ he]; exact (hn he).
  - move=>[[hg hm] hn]; split; first exact hg.
    split; first exact hm; move=>he; exact (hn (conj hg he)).
have hDR:is_measure_m_rectifiable beta r (M `\` E).
  exact (@measure_rectifiable_subset R X beta r M (M `\` E) (fun x hx=>hx.1) hMRect).
have hDS:M `\` E `<=` @euclidean_unit_sphere_set R d.+1 by move=>x hx; exact (hMS x hx.1).
have hDiffMass:=hMass (M `\` E) hDS hDR.
rewrite hDifference hSourceNull in hDiffMass.
have hTargetNull:beta (M `\` E)=0%E.
  have h:=congr1 (fun z : \bar R =>(C^-1%:E*z)%E) hDiffMass.
  by rewrite mule0 muleA -EFinM mulVf ?gt_eqF // mul1e in h.
have hMMeas:measure_measurable beta M:=
  borel_regular_borel_measurable hBeta (@hausdorff_measure_borel_regular R X r) hMB.
apply:(@measurable_set_null_modification R X beta hBeta M E (M `\` E) hTargetNull _ hMMeas).
move=>x hNot; split.
- move=>hm; apply:contrapT=>hn; exact (hNot (conj hm hn)).
- exact (hEM x).
Qed.
