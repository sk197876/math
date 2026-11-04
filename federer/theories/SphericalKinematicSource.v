(** Federer (1969), 3.2.48, p. 284: the actual
    original source X times Y is finitely Hausdorff rectifiable
    and completed measurable. Every premise of the 3.2.23
    application is derived from the printed A,B hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts ProductInner UnitSphereSpace
  SphericalProductPreimageImage SphericalOrthogonalPullback SphericalMeasurablePullback
  RectifiableSetUP RectifiableFiniteHausdorffMass HausdorffMeasure MeasureUP
  FiniteInnerCompletedCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_source]: the three source
    rectifiability assertions and source measurability needed in
    3.2.48, p. 284, first proof paragraph. Original
    completed measurable A,B, arbitrary natural k,m and the
    actual product inner metric are retained. In particular
    genuine rectifiability of B is not weakened. *)
Theorem spherical_kinematic_source (R:realType) d k m (c:R_n R d.+1)
    (A B:set (R_n R d.+1)):
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->B `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R d.+1)) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)) in
  let source:=[set z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  is_measure_m_rectifiable (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N source /\
  measure_measurable (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) source.
Proof.
move=>hc hA hB hRA hMA hRB hMB P source.
have hRBF:=rectifiable_hausdorff_measure_rectifiable hRB.
have hX:=@spherical_measurable_measure_rectifiable_pullback R d k c A hc hA hRA hMA.
have hY:=@spherical_measurable_measure_rectifiable_pullback R d m c B hc hB hRBF hMB.
have hYGenuine:=@federer_3_2_47_1 R d c B m hc hB hRB.
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R d.+1 d.+1.
exact (@finite_inner_completed_cartesian_product_right R
  (Hom (R_n R d.+1) (R_n R d.+1)) (Hom (R_n R d.+1) (R_n R d.+1)) _ _
  (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)
  _ _ e p e p (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N
  (spherical_orthogonal_preimage c A) (spherical_orthogonal_preimage c B)
  hChart hChart hX.1 hX.2 hYGenuine hY.2).
Qed.
