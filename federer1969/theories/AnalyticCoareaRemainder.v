(** Federer (1969), 3.2.33, p. 270: analytic
    impossibility of the positive critical-source remainder,
    with arbitrary natural source dimension and the original
    public partial Jacobian and fibre loci. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormAnalyticRelativeUP AnalyticSubmanifoldUP AnalyticCoareaRemainderIntegral
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction MeasureRestriction
  MeasureApproximateJacobian RectifiablePositiveFibreCoareaUP MeasureSubsetIntegral
  MeasureUP HausdorffMeasure RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_33_analytic]: the final
    paragraph of Federer 3.2.33, p. 270. For
    an analytic map on a connected analytic m-submanifold,
    the displayed critical-source remainder integral is zero.
    Retain the original X,Y and public approximate Jacobian
    from 3.2.32. The proof actually needs no global
    Lipschitz bound, and also retains mu=m and mu=0.
    Both corrected references 3.1.24 and 3.1.18
    (erratum p. 5, book p. 270 lines 25/28)
    are discharged by actual rank and fibre proofs. *)
Theorem federer_3_2_33_analytic (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  (mu<=m)%N ->@is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  @connected (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  let f:=partial_function_source_restrict W (partial_function_total F) in
  is_measure_subset_integral H
    (partial_approximate_image_dimension_locus m mu f `\`
      partial_function_preimage f (positive_partial_fibre_locus m mu f))
    (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f)) m mu f) 0%E.
Proof.
move=>hmu hW hF hConnected hRect hMeas H f.
have [l hDim]:exists l,m=(mu+l)%N by exists (m-mu)%N; rewrite subnKC.
subst m.
exact:(analytic_coarea_remainder_integral_zero hW hF hConnected hRect hMeas).
Qed.
