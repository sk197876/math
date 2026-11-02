(** Federer (1969), 3.2.33, p. 270: the smooth
    positive-remainder behavior is impossible on a connected
    analytic manifold for an analytic map. The actual
    original partial Jacobian and the X,Y of 3.2.32
    are retained in the subset integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormAnalyticRelativeUP AnalyticSubmanifoldUP RelativeDifferentialUP RelativeLowImageLocus
  AnalyticRelativeRankAlternative AnalyticNullFibreJacobian AnalyticSubmanifoldApproximateDifferential
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialImageDimensionUP MeasureApproximateDifferentialUP MeasureApproximateJacobian
  RectifiablePositiveFibreCoareaUP RestrictedPositiveFibreComplement
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureSubsetIntegral
  NullSubsetIntegral SubsetIntegralAlmostZero ExtendedRealOrderTopology HausdorffMeasure RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [analytic_coarea_remainder_integral_zero]: the
    analytic impossibility conclusion of Federer 3.2.33,
    p. 270. Actual local equations prove the intrinsic
    low-rank locus either all or null on connected W.
    In the null case the original critical source is null
    up to the proved differential-agreement exception. In
    the all case a null fibre forces the actual intrinsic
    exterior norm to vanish. Both cases give the ORIGINAL
    subset integral zero, without a totalized Jacobian,
    assumed rank alternative or fibre-positivity premise.
    The supporting statement also allows l=0 and needs
    no global Lipschitz bound beyond local analyticity. *)
Theorem analytic_coarea_remainder_integral_zero (R:realType) n mu l v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n (mu+l) W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  @connected (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (mu+l)) (mu+l) W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (mu+l)) W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (mu+l) in
  let f:=partial_function_source_restrict W (partial_function_total F) in
  is_measure_subset_integral H
    (partial_approximate_image_dimension_locus (mu+l) mu f `\`
      partial_function_preimage f (positive_partial_fibre_locus (mu+l) mu f))
    (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f)) (mu+l) mu f) 0%E.
Proof.
move=>hW hF hConnected hRect hMeas H f.
pose hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) (mu+l).
pose P:=relative_low_image_locus mu W F.
pose G:=fun x=>forall d:partial_function (R_n R n) (R_n R v),
  @has_relative_norm_differential R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT W F x d <->
  is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict H W) (mu+l) f x d.
have hGood:=@analytic_submanifold_relative_approximate_almost R n (mu+l) v W F hW hF hRect hMeas.
change (H (W `\` G)=0%E) in hGood.
have hDom:partial_function_domain f = W.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
pose A:=partial_approximate_image_dimension_locus (mu+l) mu f `\`
  partial_function_preimage f (positive_partial_fibre_locus (mu+l) mu f).
have hAW:A `<=` W.
  move=>x hx; have hxDom:=hx.1.1; by rewrite hDom in hxDom.
have hAP x (hx:A x) (hg:G x):P x.
  have [d [hApprox hLow]]:=hx.1.2.
  rewrite hDom in hApprox.
  split; first exact:hAW x hx.
  exists d; split; last exact hLow; exact:(hg d).2 hApprox.
case:(@analytic_relative_rank_bound_alternative R n (mu+l) v mu W F hW hF hConnected)=>[hAll|hNull].
- apply:(subset_integral_almost_zero hH).
  apply:(measure_null_subset hH _ hGood)=>x [hx hn].
  split; first exact:hAW x hx.
  move=>hg; apply:hn.
  have [d [hApprox hLow]]:=hx.1.2.
  rewrite hDom in hApprox.
  have hRel:=(hg d).2 hApprox.
  have hFibre:=@restricted_positive_fibre_complement_null R n v (mu+l) mu W F x
    (hAW x hx) hx.2.
  rewrite addKn in hFibre.
  have hZero:=@analytic_null_fibre_relative_jacobian_zero R n mu l v W F x d
    hW hF hAll (hAW x hx) hRel hFibre.
  rewrite /extended_measure_approximate_jacobian.
  exists (0:R); split; last reflexivity.
  apply:(measure_approximate_jacobian_graph _ _ _ _ _ _).2.
  exists d; split; last exact hZero.
  by rewrite hDom.
- apply:(@null_target_subset_integral R [the choiceType of (R_n R n:Type)] H _ A hH).
  have hUnion:=measure_null_union hH hNull hGood.
  apply:(measure_null_subset hH _ hUnion)=>x hx.
  case:(pselect (G x))=>[hg|hn].
  + left; exact:hAP x hx hg.
  + right; split; first exact:hAW x hx; exact hn.
Qed.
