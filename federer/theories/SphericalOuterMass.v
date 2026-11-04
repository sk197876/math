(** Federer (1969), 3.2.47(3), p. 283: the
    exact mass identity for every original, possibly
    nonmeasurable E whose whole actual preimage has finite
    Hausdorff rectifiability. True Borel hulls and actual
    coarea prove both bounds without assuming a null hull difference. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts FiniteInnerChartUP FiniteInnerChartCompact FiniteInnerRectifiableCoordinates
  SphericalProductPreimageImage SphericalOrthogonalProductAlgebra SphericalOrthogonalPreimageBorel
  SphericalOrthogonalConverseRectifiability SphericalBorelMass SphericalCoareaCoverLower
  RectifiableBorelHullInside RectifiableSetUP UnitSphereSpace
  HausdorffMeasure MeasureUP MeasureBasic MeasureHull TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_outer_preimage_mass_balanced]: the
    original arbitrary-set mass identity in 3.2.47(3),
    p. 283, in balanced coarea form. The source
    and target hulls are genuine equal-mass Borel supersets;
    every fibre over original E lies in the source
    hull. Original E measurability is never added. *)
Theorem spherical_outer_preimage_mass_balanced (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E) ->
  ((((Num.sqrt (2:R))^-1)^+r)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E)%E.
Proof.
move=>hc hES hRectX.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose mu:=(n*(n-1)%/2)%N.
pose m:=(r+mu)%N.
pose beta:=@hausdorff_measure R X r.
pose rho:=@hausdorff_measure R Y m.
pose iota:=@hausdorff_measure R Y mu (spherical_orthogonal_isotropy c).
pose j:=(((Num.sqrt (2:R))^-1)^+r).
have hBeta:=@hausdorff_measure_is_measure R X r.
have hRho:=@hausdorff_measure_is_measure R Y m.
have hRectE:=@spherical_orthogonal_converse_rectifiability R n c E r hc hES hRectX.
have hSphereB:@borel_set X (@euclidean_unit_sphere_set R n.+1).
  exact (closed_borel_set (compact_closed (@metric_hausdorff R X) (@euclidean_unit_sphere_compact R n.+1))).
have [Z [hZB [hHullE [hRectZ hZS]]]]:=@rectifiable_borel_measure_hull_inside R n.+1 r E
  (@euclidean_unit_sphere_set R n.+1) hRectE hSphereB hES.
have hEZ:E `<=` Z:=measure_hull_subset hHullE.
have hBaseMass:beta Z=beta E:=esym (measure_hull_equal_measure hBeta hHullE).
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R n.+1 n.+1.
pose d:=(n.+1*n.+1)%N.
pose A:=p @` (spherical_orthogonal_preimage c E).
pose B:=p @` (spherical_orthogonal_preimage c Z).
pose T:=inner_metric_space (@euclidean_inner_productP R d).
pose tau:=@hausdorff_measure R T m.
have hTau:=@hausdorff_measure_is_measure R T m.
have hRectA:=@finite_inner_chart_measure_rectifiable_coordinates R H _
  (@euclidean_hom_inner_productP R n.+1 n.+1) d e p m (spherical_orthogonal_preimage c E) hChart hRectX.
have hBB:@borel_set T B.
  exact (@finite_inner_chart_coordinates_borel R H _ (@euclidean_hom_inner_productP R n.+1 n.+1)
    d e p (spherical_orthogonal_preimage c Z) hChart (@spherical_orthogonal_preimage_borel R n.+1 c Z hZB)).
have hAB:A `<=` B.
  move=>z [g [hg hEg] <-]; exists g; last reflexivity.
  exact (conj hg (hEZ _ hEg)).
have [W [hWB [hHullW [hRectW hWZ]]]]:=@rectifiable_borel_measure_hull_inside R d m A B hRectA hBB hAB.
have hAW:A `<=` W:=measure_hull_subset hHullW.
have hSourceMass:tau W=rho (spherical_orthogonal_preimage c E).
  have hEqual:=measure_hull_equal_measure hTau hHullW.
  change (tau (p @` (spherical_orthogonal_preimage c E))=tau W) in hEqual.
  rewrite /tau (@finite_inner_chart_inverse_hausdorff R H _
    (@euclidean_hom_inner_productP R n.+1 n.+1) d e p hChart) in hEqual.
  exact (esym hEqual).
have hLower:=@spherical_coarea_cover_lower R n d r e p c E Z W
  hChart hc hES hEZ hRectZ hZB hRectW hWB hAW hWZ.
change (is_true ((iota*beta E<=j%:E*tau W)%E)) in hLower.
rewrite hSourceMass in hLower.
have hZMass:=@spherical_borel_preimage_mass_balanced R n r c Z hc hZS hRectZ hZB.
change (j%:E*rho (spherical_orthogonal_preimage c Z)=iota*beta Z)%E in hZMass.
rewrite hBaseMass in hZMass.
have hMono:(rho (spherical_orthogonal_preimage c E)<=rho (spherical_orthogonal_preimage c Z))%E.
  apply:(measure_mono hRho)=>g [hg hEg]; exact (conj hg (hEZ _ hEg)).
have hUpper:(j%:E*rho (spherical_orthogonal_preimage c E)<=iota*beta E)%E.
  rewrite -hZMass; apply:lee_wpmul2l; last exact hMono.
  rewrite lee_fin /j; apply:exprn_ge0; by rewrite invr_ge0 sqrtr_ge0.
apply/eqP; by rewrite eq_le hUpper hLower.
Qed.
