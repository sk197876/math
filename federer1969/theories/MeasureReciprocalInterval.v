(** Federer (1969), 2.4.17, p. 90: U is an interval of reciprocal exponents.
    The proof below derives the set assertion from the already proved
    interval property of P and the exponent-independent zero-norm condition.
    Logarithmic convexity remains a separate assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP InnerConvex
  MeasureExponentDomain MeasureExponentZero ReciprocalExponent ExtendedExponentInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reciprocal_exponent_normE]: supporting
    identification of the two coordinate forms in Federer 2.4.17,
    p. 90, with 1/0=infinity. *)
Lemma measure_reciprocal_exponent_normE (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : PartialFunctionUP.partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) u :
  measure_reciprocal_exponent_norm mu f u=measure_exponent_norm mu f (reciprocal_lebesgue_exponent u).
Proof. by rewrite /measure_reciprocal_exponent_norm /reciprocal_lebesgue_exponent; case: ifP. Qed.

(** Source for [measure_positive_reciprocal_interval]: the order-interval
    formulation of the U assertion in Federer 2.4.17, p. 90 *)
Lemma measure_positive_reciprocal_interval (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) -> forall u v w : R,
  measure_positive_reciprocal_exponents mu (partial_function_total f) u ->
  measure_positive_reciprocal_exponents mu (partial_function_total f) v ->
  (u <= w)%R -> (w <= v)%R ->
  measure_positive_reciprocal_exponents mu (partial_function_total f) w.
Proof.
move=> hf u v w [hu0 [hu1 [hup huf]]] [hv0 [hv1 [hvp hvf]]] huw hwv.
have hw0 := le_trans hu0 huw; have hw1 := le_trans hwv hv1.
have hru := @reciprocal_lebesgue_exponent_domain R u hu0 hu1.
have hrv := @reciprocal_lebesgue_exponent_domain R v hv0 hv1.
have hrw := @reciprocal_lebesgue_exponent_domain R w hw0 hw1.
rewrite measure_reciprocal_exponent_normE in hup huf.
rewrite measure_reciprocal_exponent_normE in hvp hvf.
have hpu : measure_finite_norm_exponents mu (partial_function_total f) (reciprocal_lebesgue_exponent u).
  exact: (conj hru huf).
have hpv : measure_finite_norm_exponents mu (partial_function_total f) (reciprocal_lebesgue_exponent v).
  exact: (conj hrv hvf).
have hpw := @measure_finite_norm_exponents_interval R X mu hm (partial_function_total f) hf
  (reciprocal_lebesgue_exponent v) (reciprocal_lebesgue_exponent u) (reciprocal_lebesgue_exponent w)
  hpv hpu (@reciprocal_lebesgue_exponent_antitone R w v hw0 hwv)
  (@reciprocal_lebesgue_exponent_antitone R u w hu0 huw).
have hnonzero := (@measure_exponent_norm_positive_iff R X mu hm f _ hru hf).1 hup.
have hwpos := (@measure_exponent_norm_positive_iff R X mu hm f _ hrw hf).2 hnonzero.
split=> //; split=> //; rewrite measure_reciprocal_exponent_normE; by split=> //; exact hpw.2.
Qed.

(** Source for [measure_positive_reciprocal_convex]: the convex set
    formulation of U being an interval in Federer 2.4.17, p. 90, explicit. *)
Theorem measure_positive_reciprocal_convex (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  @is_inner_convex R R^o (measure_positive_reciprocal_exponents mu (partial_function_total f)).
Proof.
move=> hf u v hu hv t ht ht1; have h1t : (0 <= 1-t)%R by rewrite subr_ge0.
change (measure_positive_reciprocal_exponents mu (partial_function_total f) ((1-t) * u+t * v)%R).
have [huv|hvu] := leP u v.
- have hl := lerD (lexx ((1-t) * u)%R) (ler_wpM2l ht huv).
  rewrite -mulrDl subrK mul1r in hl.
  have hh := lerD (ler_wpM2l h1t huv) (lexx (t * v)%R).
  rewrite -mulrDl subrK mul1r in hh.
  exact: (@measure_positive_reciprocal_interval R X mu hm f hf u v _ hu hv hl hh).
- have hvu' := ltW hvu.
  have hl := lerD (ler_wpM2l h1t hvu') (lexx (t * v)%R).
  rewrite -mulrDl subrK mul1r in hl.
  have hh := lerD (lexx ((1-t) * u)%R) (ler_wpM2l ht hvu').
  rewrite -mulrDl subrK mul1r in hh.
  exact: (@measure_positive_reciprocal_interval R X mu hm f hf v u _ hv hu hl hh).
Qed.
