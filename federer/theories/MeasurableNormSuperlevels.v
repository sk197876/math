(** Federer (1969), 2.3.8, p. 78: measurable norm superlevels used in gauge
    attainment. Source context and erratum convention:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity RealMetricBackground
  PartialFunctionUP PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasurablePostcomposition BorelFunctionBasic MeasureGauge MeasureGaugeAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_norm_function]: norm measurability for Federer
    2.3.8, p. 78 No essential-separability hypothesis is needed for this
    assertion. *)
Lemma measurable_norm_function (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu
    (partial_function_postcompose f (fun y => (N y : real_line_metric R))).
Proof.
move=> hf; apply: (@measurable_function_borel_postcomposition R X
  [the topologicalType of real_norm_metric_space hN] (real_line_metric R)
  mu hm f (fun y => (N y : real_line_metric R)) hf).
apply: continuous_borel_function; exact: real_norm_metric_norm_continuous.
Qed.

(** Source for [measurable_norm_superlevel]: the measurable superlevel sets
    in Federer 2.3.8, p. 78, attainment argument *)
Lemma measurable_norm_superlevel (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f -> forall r : R,
  measure_measurable mu (partial_norm_superlevel N f r%:E).
Proof.
move=> hf r.
have hn := @measurable_norm_function R X V N hN mu hm f hf.
have ho : open ([set y : real_line_metric R | (r < y)%R]) by exact: open_gt.
have h := measurable_function_open_preimage hn ho.
rewrite partial_function_postcompose_preimage in h; exact h.
Qed.

(** Source for [measurable_norm_gauge_attained]: direct second
    display of Federer 2.3.8, p. 78, for a measurable normed-
    space valued partial function. The separability and Banach
    completeness assumptions are unnecessary for this single claim. *)
Theorem measurable_norm_gauge_attained (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f ->
  measure_gauge_feasible mu N f (measure_gauge mu N f).
Proof.
move=> hf; apply: (@measure_gauge_attained R X (real_norm_metric_space hN) mu hm N f).
exact (@measurable_norm_superlevel R X V N hN mu hm f hf).
Qed.
