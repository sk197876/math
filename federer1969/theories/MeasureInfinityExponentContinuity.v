(** Federer (1969), 2.4.17, p. 90: continuity at the infinity exponent along
    finite exponents. This theorem follows those steps and treats zero and
    infinite essential norm separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureLpNorm MeasureEssentialNorm MeasureExponentDomain MeasureExponentZero
  MeasureInfinityExponentLowerContinuity MeasureInfinityExponentUpperContinuity ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinity_exponent_sequence_continuity]: infinity
    limiting-exponent case of Federer 2.4.17, p. 90 The essential norm may
    be zero, positive finite or infinite. Only the first finite exponent is
    required to have finite norm. *)
Theorem measure_infinity_exponent_sequence_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (p : nat -> R) :
  (forall n, (1 <= p n)%R) -> is_measure_measurable_function mu (partial_function_total f) ->
  measure_lp_norm mu (fun y : R => `|y|%R) (p 0%N) (partial_function_total f) < +oo ->
  extended_order_limit (fun n => (p n)%:E) +oo ->
  extended_order_limit (fun n => measure_lp_norm mu (fun y : R => `|y|%R) (p n) (partial_function_total f))
    (measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f)).
Proof.
move=> hp hf hfin hl.
split; first exact: (@measure_infinity_exponent_eventual_lower_bound R X R^o _ (scalar_absolute_value_norm R) mu hm _ p hp hf hfin hl).
move=> b hb.
pose e := measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f).
have he0 : 0 <= e := measure_essential_norm_nonnegative _ _ _.
have hefin : e < +oo := lt_le_trans hb (leey b).
have henum : e \is a fin_num by rewrite (ge0_fin_numE he0).
pose A := fine e.
have heA : e=A%:E by rewrite /A fineK.
have hA0 : (0 <= A)%R by move: he0; rewrite heA lee_fin.
have [hAz|hAz] := eqVneq A 0%R.
- have hez : measure_exponent_norm mu (partial_function_total f) +oo=0 by rewrite /= -/e heA hAz.
  have hz := (@measure_exponent_norm_zero_iff R X mu hm f +oo (leey _) hf).1 hez.
  exists 0%N=> n hindex.
  have hpn : 1 <= (p n)%:E := hp n.
  have hn := (@measure_exponent_norm_zero_iff R X mu hm f (p n)%:E hpn hf).2 hz.
  change (measure_lp_norm mu (fun y : R => `|y|%R) (p n) (partial_function_total f)=0) in hn.
  rewrite hn; by move: hb; rewrite -/e heA hAz.
have hApos : (0 < A)%R by rewrite lt_neqAle eq_sym hAz hA0.
have hepos : 0 < measure_exponent_norm mu (partial_function_total f) +oo by rewrite /= -/e heA lte_fin.
have hz := (@measure_exponent_norm_positive_iff R X mu hm f +oo (leey _) hf).1 hepos.
have hpn0 : 1 <= (p 0%N)%:E := hp 0%N.
have hBposE := (@measure_exponent_norm_positive_iff R X mu hm f (p 0%N)%:E hpn0 hf).2 hz.
pose d := measure_lp_norm mu (fun y : R => `|y|%R) (p 0%N) (partial_function_total f).
have hdpos : 0 < d := hBposE.
have hdnum : d \is a fin_num by rewrite (ge0_fin_numE (ltW hdpos)).
pose B := fine d.
have hdB : d=B%:E by rewrite /B fineK.
have hBpos : (0 < B)%R by move: hdpos; rewrite hdB lte_fin.
have hab : A%:E < b by rewrite -heA.
exact: (@measure_infinity_exponent_eventual_upper_bound R X R^o _ (scalar_absolute_value_norm R) mu hm _ (p 0%N) A B p
  (hp 0%N) hp hApos hBpos hf heA hdB hl b hab).
Qed.
