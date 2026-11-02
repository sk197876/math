(** Federer (1969), 2.5.7, p. 99: characteristic functions of finite-measure
    covering sets in the definition of tau. Their L1 norm is the measure of
    the set, by 2.4.5, p. 83, and 2.4.12, p. 86. These supporting lemmas use
    abstract characteristic laws, allowing measure zero as well as positive
    finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  MeasureUP MeasureBasic MeasurableFunctionUP CharacteristicFunctionUP MeasurableNormedCharacteristic
  MeasureCharacteristicIntegral MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  RealPower ExtendedPositivePower MeasureLpNorm MeasureRealLpMembership TotalScalarLpUP TotalScalarLpFiniteSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_characteristic_nonnegative]: positivity of the
    covering-set characteristic functions in Federer 2.5.7, p. 99 This is a
    direct consequence of the characteristic laws. *)
Lemma total_characteristic_nonnegative (R : realType) (X : Type) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> forall x, (0 <= s x)%R.
Proof.
move=> hs x; case: (pselect (A x))=> hx.
- by rewrite (characteristic_on_set hs hx) ler01.
- by rewrite (characteristic_off_set hs hx).
Qed.

(** Source for [finite_measure_characteristic_lone_norm]: the norm
    phi_(1)(1_A)=phi(A) used in Federer 2.5.7, p. 99 The proof derives the
    norm from the actual characteristic integral. *)
Lemma finite_measure_characteristic_lone_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X -> R) (b : R) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A=b%:E ->
  total_scalar_lp_norm mu 1 s=b%:E.
Proof.
move=> hs hA hb.
have hsm := (@measurable_normed_characteristic R X mu hm A s hs hA).1.
have hsi := @measure_characteristic_integral R X mu hm A s hs hA.
rewrite hb in hsi.
have hpow : is_measure_integral mu
    (partial_norm_power (fun y : R => `|y|%R) 1%R (total_scalar_function s)) b%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hsi)=> x z.
  change (partial_function_graph (real_total_integrand s) x z <->
    partial_function_graph (partial_norm_power (fun y : R => `|y|%R) 1%R (total_scalar_function s)) x z).
  rewrite real_total_integrand_graph; split.
  - move=> hz; exists (s x); split=> //.
    by rewrite real_power_one_exponent ?normr_ge0 // (ger0_norm (total_characteristic_nonnegative hs x)).
  - move=> [y [hy hz]].
    have he : s x=y := hy.
    by rewrite real_power_one_exponent ?normr_ge0 // -he (ger0_norm (total_characteristic_nonnegative hs x)) in hz.
have he := @measure_lp_norm_of_integral R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu 1%R (total_scalar_function s) b%:E hm (lexx _) hsm hpow.
have hb0 : (0 <= b)%R by have hh := measure_nonnegative hm A; rewrite hb lee_fin in hh.
by rewrite invr1 /extended_positive_power real_power_one_exponent // in he.
Qed.

(** Source for [finite_measure_characteristic_lone]: full L1 membership of
    the covering-set tests in Federer 2.5.7, p. 99 Measurability and
    countably measurable support are proved, not discarded when computing
    the norm. *)
Lemma finite_measure_characteristic_lone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X -> R) (b : R) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A=b%:E ->
  total_scalar_lp mu 1 s /\ finite_total_scalar_lp_norm mu 1 s=b.
Proof.
move=> hs hA hb.
have hn := @finite_measure_characteristic_lone_norm R X mu hm A s b hs hA hb.
have hmemb : total_scalar_lp mu 1 s.
  apply: (proj2 (@total_scalar_lp_finite_equivalence R X mu hm 1%R s)).
  exact: (@measurable_real_finite_norm_lp R X mu hm 1%R b (total_scalar_function s) (lexx _)
    (@measurable_normed_characteristic R X mu hm A s hs hA).1 hn).
split=> //; by rewrite /finite_total_scalar_lp_norm hn.
Qed.
