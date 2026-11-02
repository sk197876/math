(** Federer (1969), 3.2.22, p. 260:
    global distortion comparisons on every measurable
    subset of the original source W. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureIntegralUP MeasureSubsetIntegral MeasureUP MeasureRestriction MeasureAlmostUP HausdorffMeasure MeasureApproximateJacobian
  RectifiableSetUP MeasureRectifiableSubset RectifiableCompactChartsUP RectifiableCompactCharts
  RectifiableChartPairPieces RectifiableChartPairFamily RectifiableChartPairOmittedJacobian
  RectifiableChartPairFibreMassSum CountableScalarCutoffZeroRemainder CountableCoareaIntegralComparison
  RectifiableCoareaJacobianMeasurable RectifiableCoareaLocalIntegralComparison
  NonnegativeSum MappingMultiplicity RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_subset_comparison]:
    summation and replacement of W by a measurable
    subset in Federer 3.2.22, p. 260.
    Cover A with the source charts but keep the
    intrinsic Jacobian relative to the original W.
    The proved source and fibre sums include both
    erratum-corrected remainders. All geometric and
    measurability premises of the local comparison are
    discharged from the printed hypotheses. *)
Theorem rectifiable_coarea_subset_comparison (R:realType) m n mu v
    (lambda:R) (W A:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  (mu<=m)%N ->(1<lambda)%R ->A `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) A ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  (forall w,(0<=J0 w)%R) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  exists a b,
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) A
      (partial_function_total (fun w=>((J0 w)%:E:extended_real_line R))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun z=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F A z)
          :extended_real_line R))) b /\
    0<=a /\ 0<=b /\
    a<=(lambda^+(mu+mu+m+m))%R%:E*b /\ b<=(lambda^+(mu+mu+m+m))%R%:E*a.
Proof.
move=>hDim hLambda hAW hA hRectW hW hRectZ hZ hF hRange hJPositive hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
pose beta:=@hausdorff_measure R Y mu.
have hr:=@hausdorff_measure_is_measure R X m.
have hb:=@hausdorff_measure_is_measure R Y mu.
have hRectA:=@measure_rectifiable_subset R [the metricType R of X] rho m W A hAW hRectW.
have [K [psi hSource]]:=@federer_3_2_18 R m n lambda A hRectA hA hLambda.
have [C [gamma hTarget]]:=@federer_3_2_18 R mu v lambda Z hRectZ hZ hLambda.
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
pose N:=fun z:Y=>(@hausdorff_measure R X (m-mu) (mapping_fibre F A z):extended_real_line R).
pose Ni:=fun p:nat*nat=>fun z:Y=>(@hausdorff_measure R X (m-mu) (mapping_fibre F (P p) z):extended_real_line R).
have hSub p:P p `<=` A by move=>w [hw _]; exact:((hSource.1 p.1).2 w hw).
have hDisjoint:forall p q,setT p ->setT q ->p<>q ->P p `&` P q=set0.
  move=>p q _ _; exact:(@rectifiable_chart_pair_pieces_disjoint R m n mu v lambda A Z K psi C gamma F hSource hTarget p q).
have hZero:=rectifiable_chart_pair_omitted_jacobian_zero hAW hRectW hW hF hRange hSource hTarget hJ0.
pose Index:=(nat*nat)%type.
have hCount:countable (@setT (nat*nat)) by exact:countableP.
have hSourceSum:=@countable_scalar_cutoff_zero_remainder R [the choiceType of X]
  [the choiceType of (Index:Type)] rho hr A setT P J0 hJPositive (fun p _=>hSub p) hDisjoint hZero.
have hRangeA w:A w ->Z (F w) by move=>hw; exact:(hRange w (hAW w hw)).
have hTargetSum:=rectifiable_chart_pair_fibre_mass_sum hDim hF hSource hTarget hRangeA.
have hCutMeas:=rectifiable_coarea_jacobian_cutoff_measurable hRectW hW hRectZ hZ hF hRange hJPositive hJ0.
apply:(@countable_coarea_integral_comparison R [the choiceType of X] [the choiceType of Y]
  [the choiceType of (Index:Type)] rho beta hr hb A P J0 N Ni
  (lambda^+(mu+mu+m+m)) hCount (exprn_gt0 (mu+mu+m+m) (lt_trans ltr01 hLambda)) hJPositive
  (fun p z=>@measure_nonnegative R X _ (@hausdorff_measure_is_measure R X (m-mu)) _)
  hSourceSum hTargetSum)=>p.
have hChartW:psi p.1 @` K p.1 `<=` W.
  move=>w hw; exact:(hAW w ((hSource.1 p.1).2 w hw)).
exact:(rectifiable_coarea_local_integral_comparison hDim hLambda (hSource.1 p.1).1
  (hTarget.1 p.2).1 hChartW hW hRectW.2 hF hJPositive hJ0 hCutMeas).
Qed.
