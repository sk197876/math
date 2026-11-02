(** Federer (1969), 2.3.8, pp. 78–79: the gauge ball B(0,e). The literal
    convex-hull argument is stated on total-domain members. This restriction
    is explicit because Federer's erratum p. 1, book p. 78 line 7, corrects
    the full partial collection to a set. Source context:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP
  MeasurableNormedFunctionUP MeasurableNormedBasic TotalMeasurableFunctionSpace
  MeasureGauge MeasureGaugeComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_measure_gauge_ball]: direct B(0,e)
    definition from Federer 2.3.8, pp. 78–79, restricted
    explicitly to total-domain members for vector-space convexity. *)
Definition total_measure_gauge_ball (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (e : R) : set (GRing.Lmodule.clone R (X -> real_norm_metric_space hN) _) :=
  [set f | is_measurable_normed_function mu (partial_function_total f) /\
    measure_gauge mu N (partial_function_total f) <= e%:E].

(** Source for [total_measure_gauge_ball_zero]: the zero
    function belongs to each nonnegative-radius ball in Federer
    2.3.8, pp. 78–79, supporting the convex-hull proof. *)
Lemma total_measure_gauge_ball_zero (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (e : R) : (0 <= e)%R ->
  @total_measure_gauge_ball R X V N hN mu e (fun _ => 0%R).
Proof.
move=> he; split; first exact (@measurable_normed_total_constant R X V N hN mu hm (0%R : V)).
have hz : measure_gauge mu N (partial_function_total (fun _ : X => (0%R : V))) <= 0.
  apply: (@measure_gauge_uniform_norm_bound R X V mu hm N _ 0 (lexx _)).
  move=> x y <-; by rewrite (real_seminorm_zero hN.1).
apply: le_trans hz _; exact he.
Qed.
