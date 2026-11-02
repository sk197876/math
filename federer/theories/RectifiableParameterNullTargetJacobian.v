(** Federer (1969), 3.2.22, pp. 258–259: the
    approximate mu-Jacobian vanishes almost everywhere above
    the null target-chart remainder Q. Use a Borel null
    cover for 3.2.21 and the exact partial chain rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP LipschitzUP LinearRankUP LinearRankAtLeast
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  EuclideanLebesgueDimensions RectifiableCompactChartsUP RectifiableCompactChartLaws
  RectifiableDifferentialChartUP RectifiableChartDensityDifferential EuclideanChartAlmostPullback
  MeasureApproximateJacobianUP MeasureApproximateJacobian RectifiableDifferentialChartRankZero
  NullTargetDifferentialRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_parameter_null_target_jacobian]:
    ap J_mu f=0 above Q in Federer 3.2.22,
    pp. 258–259, at almost every compact chart parameter.
    The positive degree invokes 3.2.21 on a Borel null
    cover of Q. Rademacher gives an actual deficient-rank
    composite differential and 3.2.19 transfers it to the
    intrinsic approximate differential on its exact domain.
    No Borel premise on Q, derivative field or Jacobian
    measurability premise is added. *)
Theorem rectifiable_parameter_null_target_jacobian (R:realType) m n k q
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R k)
    (Q:set (R_n R k)) (J0:R_n R n->R):
  (0<q)%N ->1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) q Q=0%E ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    (K `&` (fun a=>Q (F (psi a)))) [set a|J0 (psi a)=0].
Proof.
move=>hQDegree hLambda hChart hKW hW hFinite hF hQ hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R k).
pose hm:=euclidean_lebesgue_is_measure R m.
pose G:=fun a:X=>(F (psi a):Z).
have hG:@is_metric_lipschitz R X Z setT G.
  have [M [hM hBound]]:=hF.
  have hPsi:=rectifiable_chart_global_bound hChart.
  exists (M*lambda); split.
  - apply:mulr_gt0; first exact hM; exact:(lt_trans ltr01 hLambda).
  - split; first exact:(mulr_ge0 (ltW hM) hPsi.1).
    move=>a b _ _; change (is_true (mdist (F (psi a):Z) (F (psi b):Z)<=
      M*lambda*mdist (a:X) (b:X))).
    apply:(le_trans (hBound.2 (psi a) (psi b) Logic.I Logic.I) _).
    rewrite -mulrA; exact:(ler_wpM2l (ltW hM) (hPsi.2 a b Logic.I Logic.I)).
have hRank:=@null_target_differential_rank R m k q G Q hQDegree hG hQ.
have hLocal:=rectifiable_chart_density_differential hLambda hChart hKW hW hFinite hF.
have hPointAE:measure_almost_everywhere_on (@hausdorff_measure R Y m) (psi @` K)
    [set w|is_rectifiable_differential_chart_point W K psi F w].
  apply:(measure_null_subset (@hausdorff_measure_is_measure R Y m) _ hLocal)=>w [hw hn].
  split; first exact hw; by move=>[_ hPoint]; exact:hn hPoint.
have hParam:=euclidean_chart_almost_pullback (uniform_compact_chart_bilipschitz hChart) hPointAE.
have hBoth:=measure_almost_everywhere_and hm
  ((measure_almost_everywhere_on_implication _ _ _).1 hParam)
  ((measure_almost_everywhere_on_implication _ _ _).1 hRank).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hm _ hBoth)=>a [hPoint hR] [ha hQa].
have [H [r [hH [hr hLess]]]]:=hR hQa.
have hNo:~linear_rank_at_least H q.
  move=>hAt; have hLe:=(linear_rank_at_leastP q hr).1 hAt.
  have hFalse:=leq_ltn_trans hLe hLess; by rewrite ltnn in hFalse.
have hJac:=@rectifiable_differential_chart_rank_zero R m n k q lambda W K psi F a H
  hChart ha (hPoint ha) hH hNo.
have hGraph:=(@measure_approximate_jacobian_graph R n k
  (measure_restrict (@hausdorff_measure R Y m) W) m q
  (partial_function_source_restrict W (partial_function_total F)) (psi a) 0).2 hJac.
exact:(hJ0 (psi a) 0 hGraph).
Qed.
