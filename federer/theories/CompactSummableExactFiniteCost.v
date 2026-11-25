(** Federer (1969), 4.1.23, p. 379:
    the simple decomposition of each step value
    is mass optimal. Integrating its pointwise norm
    identity preserves the exact total mass budget,
    rather than replacing it by a larger coordinate sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  FiniteSignedRealIntegral CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [compact_summable_exact_finite_cost]:
    the pointwise mass-optimal simple decomposition
    used in Federer 4.1.23, p. 379,
    retains its exact original integrated cost.
    The coefficient norm and compact L1 fields
    are the original objects; no separated raw-field
    quotient or completeness premise is introduced. *)
Theorem compact_summable_exact_finite_cost (R : realType)
    (X : topologicalType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) (mu : set X -> \bar R) (hm : is_measure mu)
    (I : finType) (f : @CompactSummableField.space R X V N hN mu hm)
    (g : I -> @CompactSummableField.space R X V N hN mu hm) :
  (forall x, N (@compact_summable_field_value R X V N hN mu hm f x)=
    \sum_i N (@compact_summable_field_value R X V N hN mu hm (g i) x)) ->
  @compact_summable_field_size R X V N hN mu hm f=
    \sum_i @compact_summable_field_size R X V N hN mu hm (g i).
Proof.
move=> hNorm.
pose value := @compact_summable_field_value R X V N hN mu hm.
pose size := @compact_summable_field_size R X V N hN mu hm.
have hIntegral i : is_measure_integral mu
    (real_total_integrand (fun x => N (value (g i) x))) (size (g i))%:E.
  exact: (@compact_summable_field_size_integral R X V N hN mu hm (g i)).
have hSum := @finite_signed_real_sum_integral R X I mu hm (enum I)
  (fun i x => (N (value (g i) x) : real_line_metric R))
  (fun i => size (g i)) (fun i _ => hIntegral i).
have hFunction : (fun x : X => (\sum_(i <- enum I) N (value (g i) x)
    : real_line_metric R))=(fun x => (N (value f x) : real_line_metric R)).
  apply: funext=> x; rewrite big_enum; exact: esym (@hNorm x).
rewrite hFunction big_enum in hSum.
exact: EFin_inj (measure_integral_unique
  (@compact_summable_field_size_integral R X V N hN mu hm f) hSum).
Qed.
