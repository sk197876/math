(** Federer (1969), 2.4.19, p. 91: in the bounded case Lebesgue convergence
    applies to F composed with finite-image approximants. These supporting
    lemmas require continuity only on C; convexity is used separately for
    the finite Jensen inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricSubsetBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionLimitUP
  PartialExtendedOrderLoci PartialDominatedConvergence PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableRealEmbedding ClosedRangeContinuousMeasurable JensenLimitTopology
  MeasureIntegralUP FiniteMeasureBoundedNorm MeasureBoundedConvergence ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_range_real_embedding_continuous]: supporting passage
    from the real-valued F of Federer 2.4.19, p. 91, to the scalar
    integral's extended-real topology *)
Lemma closed_range_real_embedding_continuous (R : realType) (Y : metricType R)
    (C : set Y) (F : Y -> real_line_metric R) :
  continuous (fun y : metric_subset C => F (val y)) ->
  continuous (fun y : metric_subset C => ((F (val y))%:E : extended_real_line R)).
Proof.
move=> hF y U hU.
exact: (hF y _ (@real_extended_embedding_continuous R (F (val y)) U hU)).
Qed.

(** Source for [bounded_closed_composite_integrals_converge]: the scalar
    convergence step in the bounded case of Federer 2.4.19, p. 91 The result
    is an actual integral limit, not only a bound on a selected subsequence. *)
Theorem bounded_closed_composite_integrals_converge (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu) (m M : R)
    (C : set Y) (c : metric_subset C) (F : Y -> real_line_metric R)
    (f : nat -> X -> Y) (g : X -> Y) :
  mu setT=m%:E -> closed C -> continuous (fun y : metric_subset C => F (val y)) ->
  (forall y, C y -> (0 <= F y <= M)%R) ->
  (forall n x, C (f n x)) -> (forall x, C (g x)) ->
  (forall n, is_measure_measurable_function mu (partial_function_total (f n))) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => partial_function_total (f n)) (partial_function_total g)) ->
  exists (a : nat -> R) (b : R),
    (forall n, is_measure_integral mu
      (partial_function_postcompose (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R))) (a n)%:E) /\
    is_measure_integral mu
      (partial_function_postcompose (partial_function_total g) (fun y => ((F y)%:E : extended_real_line R))) b%:E /\
    extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> hmass hC hF hbound hfC hgC hf hg hl.
pose fe n := partial_function_postcompose (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R)).
pose ge := partial_function_postcompose (partial_function_total g) (fun y => ((F y)%:E : extended_real_line R)).
have hfpre n : measure_almost_everywhere mu (partial_function_preimage (partial_function_total (f n)) C).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x); by split.
have hgpre : measure_almost_everywhere mu (partial_function_preimage (partial_function_total g) C).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (g x); by split.
have hFe := @closed_range_real_embedding_continuous R Y C F hF.
have hfme n := @measurable_continuous_closed_range_composite R X Y (extended_real_line R) mu hm C c
  (partial_function_total (f n)) (fun y => ((F y)%:E : extended_real_line R)) hC hFe (hf n) (hfpre n).
have hgme := @measurable_continuous_closed_range_composite R X Y (extended_real_line R) mu hm C c
  (partial_function_total g) (fun y => ((F y)%:E : extended_real_line R)) hC hFe hg hgpre.
pose H := partial_function_total (fun _ : X => (M%:E : extended_real_line R)).
have hH : is_measure_summable mu H.
  exists (M * m)%R; exact: (@finite_measure_constant_integral R X mu hm m M hmass).
have hdom n : measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_absolute_value (fe n)) H).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  have /andP[hpos hmax] := hbound _ (hfC n x).
  exists (F (f n x))%:E,M%:E; split.
  - exists (F (f n x))%:E; split; first by exists (f n x); split.
    by rewrite abse_EFin (ger0_norm hpos).
  - split=> //; by rewrite lee_fin.
have hlim : measure_almost_everywhere mu (partial_extended_convergence_locus fe ge).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x [u [z [hu [hz hlim]]]].
  have huC n : C (u n) by rewrite -(hu n : f n x=u n); exact: hfC.
  have hzC : C z by rewrite -(hz : g x=z); exact: hgC.
  exists (fun n => (F (u n))%:E),(F z)%:E; split.
  - move=> n; exists (u n); by split.
  - split; first by exists z; split.
    apply: real_metric_extended_order_limit.
    exact: (@relative_continuous_sequence_limit R Y (real_line_metric R) C F u z hF huC hzC hlim).
have [a [e [b [hai [hbi [hei [hel hal]]]]]]] := @measure_bounded_convergence R X mu hm fe ge H hH hfme hgme hdom hlim.
exists a,b; by split=> //; split.
Qed.
