(** Supporting the norm-limit step in Federer (1969), 2.10.15, p. 178, from
    the lower-limit inequality of 2.4.12, p. 87. The inputs here are
    nonnegative extended real functions, as required for projected volumes
    and their counting-multiplicity integrals. Positive infinity is allowed
    both pointwise and as a resulting norm. Finite exponents use Fatou on
    positive powers and then positive roots; infinity uses countable unions
    of null superlevel sets. It does not state this extended-input adapter.
    The local erratum has no entry for 2.10.15. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit
  PartialFunctionBasic PartialDominatedConvergence PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureFatouConvergent
  ExtendedPositivePower ExtendedPositivePowerOrder ExtendedPositivePowerLimit
  ExtendedPositivePowerLowerLimit ExtendedLowerLimitUP ExtendedLowerLimit
  ExtendedLowerLimitUpperBound NonnegativeExtendedExponentNormUP
  NonnegativeExtendedExponentNorm NonnegativeExtendedNormOrder NonnegativeExtendedEssentialBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_finite_norm_lower_semicontinuous]:
    supporting finite-exponent limit inequality in 2.10.15,
    p. 178, using 2.4.12, p. 87. This adapter retains
    extended-valued inputs; no finite-norm assumption is needed. *)
Theorem nonnegative_extended_finite_norm_lower_semicontinuous
    (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (F : nat -> X -> extended_real_line R) (g : X -> extended_real_line R) (p : R) :
  is_measure mu -> (1<=p)%R ->
  (forall n x, 0<=F n x) -> (forall x, 0<=g x) ->
  (forall n, is_measure_measurable_function mu (partial_function_total (F n))) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall x, extended_order_limit (fun n => F n x) (g x)) ->
  nonnegative_extended_exponent_norm mu g p%:E<=
    extended_lower_limit (fun n => nonnegative_extended_exponent_norm mu (F n) p%:E).
Proof.
move=> hm hp hF0 hg0 hF hg hlim.
have hp0 : (0<p)%R := lt_le_trans ltr01 hp.
have hip : (0<p^-1)%R by rewrite invr_gt0.
pose a n := measure_lower_integral mu
  (partial_function_total (fun x => extended_positive_power (F n x) p)).
have hdata n : is_measure_integral mu
    (partial_function_total (fun x => extended_positive_power (F n x) p)) (a n) /\
    nonnegative_extended_exponent_norm mu (F n) p%:E=extended_positive_power (a n) p^-1.
  have [_ [b [hi he]]] := @nonnegative_extended_exponent_norm_specification R X mu
    (F n) p%:E hm (hF0 n) hp (hF n).
  have hb : a n=b := measure_lower_integral_unique
    (measure_lower_integral_specification mu _) hi.2.2.
  by rewrite hb; split.
have [_ [b [hbi heG]]] := @nonnegative_extended_exponent_norm_specification R X mu
  g p%:E hm hg0 hp hg.
have hpos n : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus
      (partial_function_total (fun x => extended_positive_power (F n x) p))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (extended_positive_power (F n x) p); split=> //; exact: extended_positive_power_nonnegative.
have hl : measure_almost_everywhere mu
    (partial_extended_convergence_locus
      (fun n => partial_function_total (fun x => extended_positive_power (F n x) p))
      (partial_function_total (fun x => extended_positive_power (g x) p))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun n => extended_positive_power (F n x) p), (extended_positive_power (g x) p).
  split; first by move=> n.
  split=> //; exact: extended_positive_power_order_limit (fun n => hF0 n x) (hg0 x) hp0 (hlim x).
have hfatou := @measure_fatou_convergent_values R X mu hm _ _ a b hl hpos
  (fun n => (hdata n).1) hbi.
have ha0 n : 0<=a n.
  exact: (@nonnegative_total_integral_value_ge0 R X mu hm
    (fun x => extended_positive_power (F n x) p) (a n)
    (fun x => extended_positive_power_nonnegative (F n x) p) (hdata n).1).
have hb0 : 0<=b.
  exact: (@nonnegative_total_integral_value_ge0 R X mu hm
    (fun x => extended_positive_power (g x) p) b
    (fun x => extended_positive_power_nonnegative (g x) p) hbi).
have hroot := @extended_positive_power_monotone R b (extended_lower_limit a) p^-1 hb0 hfatou hip.
have hpower := @extended_positive_power_lower_limit R a (extended_lower_limit a) p^-1
  ha0 hip (extended_lower_limit_laws a).
have he := extended_lower_limit_unique hpower
  (extended_lower_limit_laws (fun n => extended_positive_power (a n) p^-1)).
have heF : (fun n => nonnegative_extended_exponent_norm mu (F n) p%:E)=
    (fun n => extended_positive_power (a n) p^-1).
  apply/funext=> n; exact: (hdata n).2.
by rewrite heG heF -he.
Qed.

(** Source for [nonnegative_extended_norm_pointwise_limit_bound]:
    supporting uniform bound through the pointwise norm limit in
    2.10.15, p. 178. All exponents 1<=t<=infinity are
    included. At infinity use strict essential thresholds and
    countable null unions, rather than exchanging essential suprema
    with arbitrary pointwise limits. *)
Theorem nonnegative_extended_norm_pointwise_limit_bound
    (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (F : nat -> X -> extended_real_line R) (g : X -> extended_real_line R)
    (t C : \bar R) : is_measure mu -> 1<=t ->
  (forall n x, 0<=F n x) -> (forall x, 0<=g x) ->
  (forall n, is_measure_measurable_function mu (partial_function_total (F n))) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall x, extended_order_limit (fun n => F n x) (g x)) ->
  (forall n, nonnegative_extended_exponent_norm mu (F n) t<=C) ->
  nonnegative_extended_exponent_norm mu g t<=C.
Proof.
move=> hm ht hF0 hg0 hF hg hlim hbound.
case: (ltP C +oo)=> hCfin; last exact: le_trans (leey _) hCfin.
case: t ht hbound=> [p| |] ht hbound; last by [].
- apply: le_trans (@nonnegative_extended_finite_norm_lower_semicontinuous R X mu F g p
    hm ht hF0 hg0 hF hg hlim) _.
  apply: (extended_lower_limit_eventual_upper_bound (extended_lower_limit_laws _)).
  exists 0%N=> n hn; exact: hbound.
- have hG := @nonnegative_extended_exponent_norm_specification R X mu g +oo hm hg0 ht hg.
  have hN n := @nonnegative_extended_exponent_norm_specification R X mu (F n) +oo hm (hF0 n) ht (hF n).
  have hC0 : 0<=C.
    exact: le_trans (nonnegative_extended_exponent_norm_nonnegative (hN 0%N)) (hbound 0%N).
  apply/lee_addgt0Pr=> e he.
  have hCf : C \is a fin_num.
    by rewrite fin_numElt (lt_le_trans (ltNyr 0) hC0) hCfin.
  have hr : C<C+e%:E.
    by rewrite -(fineK hCf) -EFinD lte_fin ltrDl.
  apply: hG.1; split; first exact: le_trans hC0 (ltW hr).
  have hnull n : mu [set x | C+e%:E<F n x]=0.
    exact: (@nonnegative_extended_essential_strict_upper R X mu hm (F n) _ _
      (hN n) (le_lt_trans (hbound n) hr)).2.
  have hU : mu (\bigcup_n [set x | C+e%:E<F n x])=0.
    exact (@measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm
      setT (fun n => [set x | C+e%:E<F n x]) (countableP _) (fun n _ => hnull n)).
  apply: (@measure_null_subset R X mu hm _ _ _ hU)=> x hx.
  have [N hN'] := (hlim x).1 _ hx.
  exists N=> //; exact: hN' N (leqnn N).
Qed.
