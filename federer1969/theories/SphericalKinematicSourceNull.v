(** Federer (1969), 3.2.48, p. 285: the null remainders
    of the two manifold covers give a null remainder in the actual
    source product. The genuine second-factor hypothesis supplies the
    exact Cartesian measure; arbitrary completed measurable sets remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts ProductInner UnitSphereSpace SphericalProductPreimageImage SphericalOrthogonalPullback
  SphericalMeasurablePullback SphericalOrthogonalPullback RectifiableSetUP RectifiableFiniteHausdorffMass
  HausdorffMeasure MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureBasic
  MeasureSplit ProductMeasure EuclideanCartesianAlmost FiniteInnerCompletedCartesianMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_source_null_factor]: the
    actual whole source is null if either original factor has zero
    Hausdorff mass, as used in 3.2.48, p. 285. The genuine B
    hypothesis gives the actual Cartesian measure equality; it is
    not weakened to merely finite-measure rectifiability. *)
Theorem spherical_kinematic_source_null_factor (R:realType) d k m (c:R_n R (1+d))
    (A B:set (R_n R (1+d))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  ((@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) k A=0)%E \/
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B=0)%E) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))
    [set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
      spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2]=0)%E.
Proof.
move=>hc hA hB hRA hMA hRB hMB hNull P.
pose S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
  spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2].
pose X:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose HX:=@hausdorff_measure R X (k+d*(d-1)%/2).
pose HY:=@hausdorff_measure R X (m+d*(d-1)%/2).
pose HP:=@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)).
pose hAlpha:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X (k+d*(d-1)%/2))
  (spherical_orthogonal_preimage c A).
pose hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X (m+d*(d-1)%/2))
  (spherical_orthogonal_preimage c B).
have hPullA:=@spherical_measurable_measure_rectifiable_pullback R d k c A hc hA hRA hMA.
have hPullB:=@spherical_measurable_measure_rectifiable_pullback R d m c B hc hB
  (rectifiable_hausdorff_measure_rectifiable hRB) hMB.
have hGenuine:=@federer_3_2_47_1 R d c B m hc hB hRB.
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R (1+d)%N (1+d)%N.
have hMeasure:=@finite_inner_completed_cartesian_measure_right R
  (Hom (R_n R (1+d)) (R_n R (1+d))) (Hom (R_n R (1+d)) (R_n R (1+d))) _ _
  (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))
  _ _ e p e p (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N
  (spherical_orthogonal_preimage c A) (spherical_orthogonal_preimage c B)
  hChart hChart hPullA.1 hPullA.2 hGenuine hPullB.2.
have hWhole:(setT:set (X*X))=(setT:set X) `*` (setT:set X).
  by apply/seteqP; split=>z _; [split|exact I].
have hBound:=product_measure_rectangle_bound hAlpha hBeta
  (MeasureSplit.measure_measurable_whole hAlpha) (MeasureSplit.measure_measurable_whole hBeta).
have hProductNull:(product_measure hAlpha hBeta setT=0)%E.
  rewrite -hWhole in hBound.
  have hTotalA:(measure_restrict HX (spherical_orthogonal_preimage c A) setT)=HX (spherical_orthogonal_preimage c A).
    by rewrite /measure_restrict setIT.
  have hTotalB:(measure_restrict HY (spherical_orthogonal_preimage c B) setT)=HY (spherical_orthogonal_preimage c B).
    by rewrite /measure_restrict setIT.
  rewrite hTotalA hTotalB in hBound.
  have hZero:(HX (spherical_orthogonal_preimage c A)*HY (spherical_orthogonal_preimage c B)=0)%E.
    case:hNull=>hNull.
    - have h:=@federer_3_2_47_2 R d c A k hc hA hNull.
      change (HX (spherical_orthogonal_preimage c A)=0)%E in h; by rewrite h mul0e.
    - have h:=@federer_3_2_47_2 R d c B m hc hB hNull.
      change (HY (spherical_orthogonal_preimage c B)=0)%E in h; by rewrite h mule0.
  rewrite hZero in hBound.
  apply/eqP; rewrite eq_le hBound; exact (measure_nonnegative (product_measure_is_measure hAlpha hBeta) _).
have hAt:=congr1 (fun nu:set (X*X)->\bar R=>nu setT) hMeasure.
have hResult:=eq_trans hAt hProductNull.
by rewrite /measure_restrict setIT in hResult.
Qed.
