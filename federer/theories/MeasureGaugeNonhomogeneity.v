(** Federer (1969), 2.3.8, p. 78: the gauge is not homogeneous. This local
    witness uses counting measure on a one-point space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic CountingMeasure
  MeasurableNormedFunctionUP FiniteCountingFunctionExamples MeasureGauge MeasureGaugeConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_counting_constant_gauge]: supporting instance
    of the characteristic formula in Federer 2.3.8, p. 78:
    on a point of mass one, a nonnegative constant c has gauge
    min(c,1). *)
Lemma unit_counting_constant_gauge (R : realType) (c : R) : (0 <= c)%R ->
  measure_gauge (@counting_measure R unit) (fun y : R => `|y|%R)
    (partial_function_total (fun _ => c)) = Order.min c%:E 1.
Proof.
move=> hc; rewrite (@measure_gauge_total_constant R unit R _
  (counting_measure_is_measure R unit)) ?normr_ge0 //.
by rewrite ger0_norm // counting_unit_whole_value.
Qed.

(** Source for [measure_gauge_not_homogeneous]: concrete witness to
    Federer's nonhomogeneity assertion, 2.3.8, p. 78 Both constants are
    members of A(mu,R), and doubling the constant one leaves its gauge equal
    to one instead of doubling it. *)
Theorem measure_gauge_not_homogeneous (R : realType) :
  let M := real_norm_metric_space (scalar_absolute_value_norm R) in
  let mu := @counting_measure R unit in
  exists f : unit -> M,
    @is_measurable_normed_function R unit R^o _ (scalar_absolute_value_norm R) mu (partial_function_total f) /\
    @is_measurable_normed_function R unit R^o _ (scalar_absolute_value_norm R) mu (partial_function_total (fun x => (2 * f x)%R)) /\
    measure_gauge mu (fun y : R => `|y|%R)
      (partial_function_total (fun x => (2 * f x)%R)) <>
      2%:E * measure_gauge mu (fun y : R => `|y|%R) (partial_function_total f).
Proof.
move=> M mu; exists (fun _ => (1%R : M)); split.
- exact (@finite_source_normed_counting_function R unit R^o _ (scalar_absolute_value_norm R) _).
split; first exact (@finite_source_normed_counting_function R unit R^o _ (scalar_absolute_value_norm R) _).
change (measure_gauge mu (fun y : R => `|y|%R)
  (partial_function_total (fun _ : unit => (2*1)%R)) <>
  2%:E * measure_gauge mu (fun y : R => `|y|%R) (partial_function_total (fun _ : unit => 1%R))).
rewrite mulr1 !unit_counting_constant_gauge ?ler0n // minxx min_r ?lee_fin ?ler1n // mule1.
move=> he; have ht : (1 : \bar R) < 2%:E by rewrite lte_fin ltr1n.
by rewrite he ltxx in ht.
Qed.
