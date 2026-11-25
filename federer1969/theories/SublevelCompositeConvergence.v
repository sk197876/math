(** Federer (1969), 2.4.19, p. 91: scalar integral convergence along the
    closed sublevel exhaustion. In the equivalent fixed-measure cutoff
    implementation, F(g_n) is bounded by F(g)+F(c); this is summable when
    the target integral is finite. The infinite case is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricSubsetBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionLimitUP
  ExtendedRealPartial PartialExtendedArithmetic PartialExtendedOrderLoci PartialDominatedConvergence PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableRealEmbedding ClosedRangeContinuousMeasurable JensenLimitTopology
  MeasureIntegralUP MeasureIntegralAddition MeasureIntegralUniqueness FiniteMeasureBoundedNorm BoundedClosedCompositeConvergence MeasureBoundedConvergence ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sublevel_composite_integrals_converge]: scalar convergence
    supporting the final limit in Federer 2.4.19, p. 91 The cutoff outside
    each inverse-image set is a fixed reference value, as explained in
    JensenSublevelApproximation.v. *)
Theorem sublevel_composite_integrals_converge (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu) (m M b : R)
    (C : set Y) (c : metric_subset C) (F : Y -> real_line_metric R)
    (f : nat -> X -> Y) (g : X -> Y) :
  mu setT=m%:E -> closed C -> continuous (fun y : metric_subset C => F (val y)) ->
  (forall y, C y -> (0 <= F y)%R) ->
  (forall n x, C (f n x)) -> (forall x, C (g x)) ->
  (forall n, is_measure_measurable_function mu (partial_function_total (f n))) ->
  is_measure_integral mu
    (partial_function_postcompose (partial_function_total g) (fun y => ((F y)%:E : extended_real_line R))) b%:E ->
  (forall n x, (F (f n x) <= F (g x)+M)%R) ->
  (forall x, (fun n => f n x) @ \oo --> g x) ->
  exists a : nat -> R,
    (forall n, is_measure_integral mu
      (partial_function_postcompose (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R))) (a n)%:E) /\
    extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> hmass hC hF hpos hfC hgC hf hgi hbound hl.
pose fe n := partial_function_postcompose (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R)).
pose ge := partial_function_postcompose (partial_function_total g) (fun y => ((F y)%:E : extended_real_line R)).
have hfpre n : measure_almost_everywhere mu (partial_function_preimage (partial_function_total (f n)) C).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x); by split.
have hFe := @closed_range_real_embedding_continuous R Y C F hF.
have hfme n := @measurable_continuous_closed_range_composite R X Y (extended_real_line R) mu hm C c
  (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R)) hC hFe (hf n) (hfpre n).
pose k := partial_function_total (fun _ : X => (M%:E : extended_real_line R)).
pose H := partial_extended_function_add ge k.
have hk := @finite_measure_constant_integral R X mu hm m M hmass.
have hH : is_measure_summable mu H.
  exists (b+M * m)%R.
  apply: (@measure_integral_add R X mu hm ge k b%:E (M * m)%R%:E _ hgi hk).
  by rewrite /extended_add /=.
have hdom n : measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_absolute_value (fe n)) H).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (F (f n x))%:E,(F (g x)+M)%R%:E; split.
  - exists (F (f n x))%:E; split; first by exists (f n x); split.
    by rewrite abse_EFin (ger0_norm (hpos _ (hfC n x))).
  - split; last by rewrite lee_fin; exact: hbound.
    apply/partial_extended_function_add_graph; exists (F (g x))%:E,M%:E; split; first by exists (g x); split.
    split=> //; by rewrite /extended_add /=.
have hlim : measure_almost_everywhere mu (partial_extended_convergence_locus fe ge).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun n => (F (f n x))%:E),(F (g x))%:E; split.
  - move=> n; exists (f n x); by split.
  - split; first by exists (g x); split.
    apply: real_metric_extended_order_limit.
    exact: (@relative_continuous_sequence_limit R Y (real_line_metric R) C F
      (fun n => f n x) (g x) hF (fun n => hfC n x) (hgC x) (hl x)).
have [a [e [d [hai [hdi [hei [hel hal]]]]]]] := @measure_bounded_convergence R X mu hm fe ge H hH hfme hgi.1 hdom hlim.
have hd := measure_integral_unique hdi hgi.
exists a; split=> //; by rewrite -hd.
Qed.
