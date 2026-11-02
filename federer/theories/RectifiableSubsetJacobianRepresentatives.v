(** Federer (1969), 3.2.32, pp. 269–270: supporting
    equality of auxiliary total Jacobian representatives on
    measurable source pieces. The public partial graphs stay exact. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  MeasureApproximateJacobian RectifiableApproximateJacobianValues RectifiableSubsetApproximateData.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_subset_jacobian_representatives_agree]:
    supporting the original-Jacobian integral in Federer 3.2.32,
    p. 269. Exact restricted graph agreement and an actual
    original Jacobian value identify any two total representatives
    almost everywhere on S. Their exceptional values are immaterial. *)
Lemma rectifiable_subset_jacobian_representatives_agree (R:realType) m n v q
    (W S:set (R_n R n)) (F:R_n R n->R_n R v) (J K:R_n R n->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S ->
  S `<=` W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  is_partial_function_total_extension (measure_approximate_jacobian
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    m q (partial_function_source_restrict W (partial_function_total F))) J ->
  is_partial_function_total_extension (measure_approximate_jacobian
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S)
    m q (partial_function_source_restrict S (partial_function_total F))) K ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S [set x|K x=J x].
Proof.
move=>hRect hW hS hSW hF hJ hK.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hData:=@rectifiable_subset_approximate_data_agreement R m n v W S F q hRect hW hS hSW hF.
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v q W F hRect hW hF.
have hBoth:=measure_almost_everywhere_and hH
  ((measure_almost_everywhere_on_implication _ _ _).1 hData)
  ((measure_almost_everywhere_on_implication _ _ _).1 hValues).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hBoth)=>x [hDx hVx] hx.
have [j hj]:=hVx (hSW x hx).
have hGraph:=measure_approximate_jacobian_graph.
have hWj:=(@measure_approximate_jacobian_graph R n v _ m q _ x j).2 hj.
have hSj:=((hDx hx).2 j).1 hWj.
exact:(eq_trans (hK x j hSj) (esym (hJ x j hWj))).
Qed.
