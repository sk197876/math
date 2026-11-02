(** Federer (1969), 3.2.32, pp. 269–270: coarea
    on a measurable source piece, retaining the approximate
    Jacobian of the original source W. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  MeasureApproximateJacobian MeasureApproximateJacobianLaws NonnegativePartialRealExtension
  MeasureRectifiableSubset MeasureIntegralUP MeasureSubsetIntegral MappingMultiplicity ExtendedRealOrderTopology
  RectifiableCoareaSubsetFormula RectifiableSubsetJacobianRepresentatives SubsetIntegralAlmostAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_restricted_coarea_integral]: the application
    of 3.2.22 to source preimages in Federer 3.2.32,
    p. 270, with the original approximate Jacobian preserved.
    Source measurability is explicit here and proved from Borel
    target pieces in the final theorem, rather than assumed there. *)
Theorem rectifiable_restricted_coarea_integral (R:realType) m n mu v
    (W S:set (R_n R n)) (Z:set (R_n R v)) (F:R_n R n->R_n R v) (J:R_n R n->R):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S ->
  S `<=` W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  (forall x,S x ->Z (F x)) ->
  is_partial_function_total_extension (measure_approximate_jacobian
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    m mu (partial_function_source_restrict W (partial_function_total F))) J ->
  exists a,is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) S
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
        (mapping_fibre F S y):extended_real_line R))) a.
Proof.
move=>hDim hRect hW hS hSW hRectZ hZ hF hRange hJ.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hRectS:=@measure_rectifiable_subset R (inner_metric_space (@euclidean_inner_productP R n))
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m W S hSW hRect.
pose d:=measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) S) m mu
  (partial_function_source_restrict S (partial_function_total F)).
have hPositive x j:partial_function_graph d x j ->(0<=j)%R.
  move=>h; exact:(measure_approximate_jacobian_nonnegative h).
have [K [hKPos hK]]:=nonnegative_partial_real_extension hPositive.
have [a [hSource hTarget]]:=@rectifiable_coarea_subset_formula R m n mu v S S Z F K
  hDim (fun x hx=>hx) hS hRectS hS hRectZ hZ hF hRange hKPos hK.
have hEqual:=@rectifiable_subset_jacobian_representatives_agree R m n v mu W S F J K
  hRect hW hS hSW hF hJ hK.
exists a; split; last exact hTarget.
apply:(subset_integral_almost_agreement hH _ hSource).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _
  ((measure_almost_everywhere_on_implication _ _ _).1 hEqual))=>x hx hSx.
exists (K x)%:E; split; first reflexivity.
change ((J x)%:E=(K x)%:E); by rewrite (hx hSx).
Qed.
