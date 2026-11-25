(** Supporting unbounded-input norm limit for Federer (1969), 2.10.9, p.
    175, from 2.4.17, p. 90. If the norm at one is infinite, probability
    monotonicity makes every later norm infinite. Otherwise finite norm
    implies finite input almost everywhere; only then may the exact scalar
    adapter be used at all exponents. No infinite values are discarded
    without a null-set proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasurableFunctionUP NonnegativeExtendedExponentNorm
  NonnegativeExtendedScalarNorm NonnegativeExtendedNormFiniteValues
  ProbabilityNonnegativeExtendedNorm ProbabilityScalarNormLeftContinuity
  MeasureExponentDomain ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_nonnegative_extended_norm_left_sequence_limit]:
    supporting all-input probability norm limit for Federer
    2.10.9, p. 175. The input and the limit norm may be
    infinite; real exponents stay in [1,t] and approach t,
    which may itself be infinity. No integrability hypothesis
    is added to the nonnegative measurable input. *)
Theorem probability_nonnegative_extended_norm_left_sequence_limit
    (R : realType) (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (p : nat -> R) (t : \bar R) :
  mu setT = 1 -> (forall x, 0<=f x) ->
  (forall n, (1<=p n)%R /\ (p n)%:E<=t) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  extended_order_limit (fun n => (p n)%:E) t ->
  extended_order_limit (fun n => nonnegative_extended_exponent_norm mu f (p n)%:E)
    (nonnegative_extended_exponent_norm mu f t).
Proof.
move=> hprob hf0 hp hf hlim.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
case: (ltP (nonnegative_extended_exponent_norm mu f 1) +oo)=> [hfin|hinf]; last first.
  have hvalue u : 1<=u -> nonnegative_extended_exponent_norm mu f u=+oo.
    move=> hu; apply/eqP; rewrite eq_le leey /=.
    exact: le_trans hinf (@probability_nonnegative_extended_norm_monotone R X mu hm f 1 u
      hprob (fun x => hf0 x) (lexx 1) hu hf).
  rewrite (hvalue t ht); split.
  - move=> a ha; exists 0%N=> n _; by rewrite (hvalue (p n)%:E (hp n).1).
  - move=> b hb; by rewrite ltNge leey in hb.
have hs := @nonnegative_extended_exponent_norm_specification R X mu f 1 hm hf0 (lexx 1) hf.
have hfinite := @finite_nonnegative_extended_norm_almost_finite R X mu hm f 1 _ hf0 hs hfin.
pose g (x : X) : real_norm_metric_space (scalar_absolute_value_norm R) := fine (f x).
have hg := @measurable_extended_finite_scalar R X mu hm f hf.
have he u : 1<=u -> nonnegative_extended_exponent_norm mu f u=
    measure_exponent_norm mu (partial_function_total g) u.
  move=> hu; exact: (@nonnegative_extended_norm_almost_finite_scalar R X mu hm f u
    hf0 hfinite hu hf).
have hgfin : measure_exponent_norm mu (partial_function_total g) 1< +oo.
  by rewrite -(he 1 (lexx 1)).
have hl := @probability_scalar_norm_left_sequence_limit R X mu hm g p t hprob hp hg hgfin hlim.
have hseq : (fun n => nonnegative_extended_exponent_norm mu f (p n)%:E)=
    (fun n => measure_exponent_norm mu (partial_function_total g) (p n)%:E).
  apply: funext=> n; exact: he (p n)%:E (hp n).1.
by rewrite hseq (he t ht).
Qed.
