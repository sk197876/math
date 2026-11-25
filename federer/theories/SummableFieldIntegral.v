(** Federer (1969), 4.1.19, p. 377: the full
    L1 carrier retains the original norm integral
    and countable-measurability condition of 2.4.12.
    This supplies the literal integral in the dual bound. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP
  PartialFunctionBasic PartialNormPower RealPower
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm
  MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureLoneNormIntegralGeneral SummableRealFunctionUP
  SummableFieldSealed SummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SummableFieldIntegral.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation value := (@summable_field_value R X V N hN mu hm).
Local Notation size := (@summable_field_size R X V N hN mu hm).

(** Source for [summable_field_lone]: the full
    original L1 conditions, including countable
    measurability, 2.4.12, p. 86, are retained
    in the extension of Federer 4.1.19, p. 377. *)
Theorem summable_field_lone (f : W) :
  @is_measure_lp_function R X V N hN mu 1
    (partial_function_total (value f)).
Proof.
have hMeas := @summable_field_measurable R X V N hN mu hm f.
have hFinite := @summable_field_finite R X V N hN mu hm f.
split; first exact: lexx.
split; first exact: hMeas.
split; first exact: hFinite.
exact: (@finite_lp_norm_countably_measurable R X V N hN mu hm 1
  (partial_function_total (value f)) (lexx 1) hMeas.1 hFinite).
Qed.

(** Source for [summable_field_size_integral]: the
    L1 size is the literal integral of the
    supplied original norm, 2.4.12, pp. 86–87,
    used in Federer 4.1.19, p. 377. *)
Theorem summable_field_size_integral (f : W) :
  is_measure_integral mu (real_total_integrand (fun x => N (value f x)))
    (size f)%:E.
Proof.
have hMeas := @summable_field_measurable R X V N hN mu hm f.
have hIntegral := @measurable_lone_norm_integral R X V N hN mu hm
  (partial_function_total (value f)) hMeas.1.
have hExact : measure_lp_norm mu N 1 (partial_function_total (value f))=(size f)%:E.
  exact: (esym (@summable_field_size_exact R X V N hN mu hm f)).
rewrite hExact in hIntegral.
apply: (@measure_integral_graph_equivalent R X mu _ _ (size f)%:E _ hIntegral).
move=> x y; split.
- move=> [v [hV hY]]; apply/real_total_integrand_graph.
  have hValue : value f x = v := hV.
  rewrite -hValue in hY.
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)) in hY.
- move/real_total_integrand_graph=> hY.
  exists (value f x); split; first by [].
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)).
Qed.
End SummableFieldIntegral.
