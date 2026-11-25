(** Federer (1969), 3.2.22, pp. 259–260:
    measurability of the intrinsic lower-degree approximate
    Jacobian, retaining its exact original partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality RestrictedAlmostEverywhere
  MeasurableFunctionUP MeasurableAlmostModification BorelRegularMeasureUP HausdorffClosedCoverAgreement
  RectifiableSetUP HausdorffMeasure MeasureApproximateJacobian
  RectifiableApproximateJacobianValues NonnegativePartialRealExtension TotalScalarCutoff
  RectifiableBorelJacobianApproximation PowerSandwichMeasurability RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coarea_jacobian_cutoff_measurable]:
    justify the source integrals in Federer 3.2.22,
    pp. 259–260. The zero-off-W total representative
    of the intrinsic mu-Jacobian is a measurable limit
    of the Borel chart-pair approximations. No initial
    measurability or change of the public partial domain
    is assumed. *)
Theorem rectifiable_coarea_jacobian_cutoff_measurable (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  (forall w,0<=J0 w) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of real_line_metric R]
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total (total_scalar_cutoff W J0)).
Proof.
move=>hRectW hW hRectZ hZ hF hRange hNonnegative hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose rho:=@hausdorff_measure R X m.
have hr:=@hausdorff_measure_is_measure R X m.
pose p:=total_scalar_cutoff W J0.
have hPos:forall w,0<=p w.
  move=>w; have [hw|hw]:=pselect (W w).
  - rewrite /p (total_scalar_cutoff_on J0 hw); exact:(hNonnegative w).
  - by rewrite /p (total_scalar_cutoff_off J0 hw).
apply:(@power_sandwich_measurability R [the choiceType of X] rho mu p hr hPos)=>lambda hLambda.
have [h [hB [hPositive [hOff hBounds]]]]:=rectifiable_borel_jacobian_approximation
  hLambda hRectW hW hRectZ hZ hF hRange hJ0.
exists h; split.
- constructor.
  + rewrite partial_function_total_domain; exact:(measure_almost_everywhere_true hr).
  + move=>U hU; rewrite partial_function_total_preimage.
    exact:(borel_regular_borel_measurable hr (@hausdorff_measure_borel_regular R X m) (hB U hU)).
- apply:(measure_almost_everywhere_mono hr _
    ((measure_almost_everywhere_on_implication _ _ _).1 hBounds))=>w hBw.
  change ((lambda^+mu)^-1* p w<=h w /\ h w<=lambda^+mu* p w).
  have [hw|hw]:=pselect (W w).
  + rewrite /p (total_scalar_cutoff_on J0 hw); exact:(hBw hw).
  + by rewrite /p (total_scalar_cutoff_off J0 hw) (hOff w hw) !mulr0.
Qed.

(** Source for [rectifiable_coarea_jacobian_measurable]:
    intrinsic ap J_mu f in Federer 3.2.22,
    p. 258 and the integrals on pp. 259–260,
    is H^m restricted to W measurable on its exact
    partial domain. Almost-everywhere actual approximate
    differentiation supplies that domain; completeness
    transfers measurability from the total cutoff witness.
    Exceptional undefined points are never filled in
    the public approximate Jacobian. *)
Theorem rectifiable_coarea_jacobian_measurable (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of real_line_metric R]
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))).
Proof.
move=>hRectW hW hRectZ hZ hF hRange.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose rho:=@hausdorff_measure R X m.
pose nu:=measure_restrict rho W.
have hr:=@hausdorff_measure_is_measure R X m.
have hn:=measure_restrict_is_measure hr W.
pose d:=measure_approximate_jacobian nu m mu (partial_function_source_restrict W (partial_function_total F)).
have hPos w j:partial_function_graph d w j ->0<=j.
  exact:(@measure_approximate_jacobian_nonnegative R n v nu m mu _ w j).
have [J [hJPos hJExt]]:=nonnegative_partial_real_extension hPos.
pose p:=total_scalar_cutoff W J.
have hMeas:=rectifiable_coarea_jacobian_cutoff_measurable hRectW hW hRectZ hZ hF hRange hJPos hJExt.
have hRestricted:@is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] nu (partial_function_total p).
  constructor.
  - rewrite partial_function_total_domain; exact:(measure_almost_everywhere_true hn).
  - move=>U hU; exact:(measure_restrict_measurable W (measurable_function_open_preimage hMeas hU)).
apply:(measurable_function_almost_equal hn hRestricted).
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v mu W F hRectW hW hF.
apply:(restricted_almost_everywhere_iff _ _ _).2.
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hValues))=>w hValue hw.
have [j hj]:=hValue hw.
have hGraph:=(@measure_approximate_jacobian_graph R n v nu m mu _ w j).2 hj.
exists j; split; last exact hGraph.
change (p w=j); rewrite /p (total_scalar_cutoff_on J hw); exact:(hJExt w j hGraph).
Qed.
