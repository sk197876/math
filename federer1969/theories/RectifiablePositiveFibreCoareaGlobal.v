(** Federer (1969), 3.2.32, pp. 269–270: both
    conclusions for an auxiliary globally Lipschitz map restricted
    to the exact original finite measurable rectifiable source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  MeasureApproximateDifferentialUP MeasureApproximateJacobian PartialImageDimensionUP
  MeasureIntegralUP MeasureSubsetIntegral MappingMultiplicity ExtendedRealOrderTopology
  NonnegativePartialRealExtension RectifiableApproximateJacobianValues SubsetIntegralAlmostAgreement
  RectifiablePositiveFibreCover RectifiableTargetCoverRank RectifiablePositiveFibreCoverIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_positive_fibre_coarea_global]: the
    complete corollary Federer 3.2.32, pp. 269–270, for
    the original source restriction of an auxiliary global map.
    The actual image dimension is at most mu almost everywhere
    above positive-mass fibres. The actual partial original Jacobian
    has a subset integral equal to the full target fibre integral.
    All source restrictions, Borel hulls, null excess and countable
    integration are discharged; no target hypothesis or completed
    source preimage-measurability premise remains. *)
Theorem rectifiable_positive_fibre_coarea_global (R:realType) m n mu v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  let Y:set (R_n R v):=[set y|0<@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F W y)] in
  let A:=W `&` F @^-1` Y in
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) A [set x|
      exists d,is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
        m (partial_function_source_restrict W (partial_function_total F)) x d /\
        is_partial_image_dimension_at_most mu d] /\
  exists a,is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) A
      (extended_measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
        (partial_function_source_restrict W (partial_function_total F))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
        (mapping_fibre F W y):extended_real_line R))) a.
Proof.
move=>hDim hRect hW hF Y A.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose f:=partial_function_source_restrict W (partial_function_total F).
pose d:=measure_approximate_jacobian (measure_restrict H W) m mu f.
have hH:=@hausdorff_measure_is_measure R X m.
have [D hCover]:=@rectifiable_positive_fibre_cover_exists R m n mu v W F hDim hRect hW hF.
split; first exact:(rectifiable_target_cover_image_dimension hRect hW hF hCover).
have hNonnegative x j:partial_function_graph d x j ->(0<=j)%R.
  exact:(@measure_approximate_jacobian_nonnegative R n v (measure_restrict H W) m mu f x j).
have [J [hPositive hJ]]:=nonnegative_partial_real_extension hNonnegative.
have [a [hSource hTarget]]:=@rectifiable_positive_fibre_cover_integral R m n mu v W F J D
  hDim hRect hW hF hPositive hJ hCover.
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v mu W F hRect hW hF.
have hAgreement:measure_almost_everywhere_on H A
    (partial_function_agreement (partial_function_total (fun x=>((J x)%:E:extended_real_line R)))
      (extended_measure_approximate_jacobian (measure_restrict H W) m mu f)).
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hH _
    ((measure_almost_everywhere_on_implication _ _ _).1 hValues))=>x hx [hWx _].
  have [j hj]:=hx hWx.
  have hGraph:=(@measure_approximate_jacobian_graph R n v (measure_restrict H W) m mu f x j).2 hj.
  have hJx:J x=j:=hJ x j hGraph.
  exists j%:E; split; first by change ((J x)%:E=j%:E); rewrite hJx.
  exists j; by split.
exists a; split; last exact hTarget.
exact:(subset_integral_almost_agreement hH hAgreement hSource).
Qed.
