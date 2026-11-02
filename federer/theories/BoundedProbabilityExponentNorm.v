(** Supporting scalar exponent facts for Federer (1969), 2.10.5, p. 172,
    last paragraph. A bounded measurable function on a probability space has
    finite norm at every exponent in [1,infinity]. Thus the continuity on
    Closure P proved in 2.4.17, p. 90, applies on this whole interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureSplit MeasurableFunctionUP MeasureGauge
  MeasureLpNorm MeasureEssentialNormUP MeasureEssentialNorm MeasureExponentDomain
  ExtendedRealOrderTopology CountableOrderIntervals BoundedSupportLp MeasureExponentContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_probability_exponent_norm_finite]:
    supporting finiteness at all exponents for
    the bounded f_S paragraph of Federer 2.10.5,
    p. 172. The uniform bound may be any
    positive real M; zero functions are included. *)
Lemma bounded_probability_exponent_norm_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (M : R)
    (t : \bar R) :
  mu setT = 1 -> (0<M)%R -> (forall x, (`|g x|<=M)%R) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_exponent_norm mu (partial_function_total g) t < +oo.
Proof.
move=> hprob hM hgM ht hg; case: t ht=> [p| |] ht //=.
- apply: (@bounded_finite_support_lp_norm R X mu hm p M setT g).
  - by move: ht; rewrite lee_fin.
  - exact hM.
  - exact: measure_measurable_whole hm.
  - by rewrite hprob ltry.
  - exact hg.
  - by move=> x [].
  - exact hgM.
- apply: le_lt_trans _ (ltry M); apply: measure_essential_norm_bound.
  split; first by rewrite lee_fin; exact: ltW hM.
  have he : partial_norm_superlevel (fun y : R => `|y|%R)
      (partial_function_total g) M%:E = set0.
    apply/seteqP; split=> x; last by [].
    move=> [y [hy hlt]]; have hy' : g x=y := hy.
    have hl : (M<`|y|)%R := hlt.
    rewrite -hy' in hl.
    by have := lt_le_trans hl (hgM x); rewrite ltxx.
  rewrite he; exact: measure_empty hm.
Qed.

(** Source for [bounded_probability_exponent_norm_continuous]:
    supporting complete exponent continuity needed
    for bounded f_S in Federer 2.10.5, p. 172,
    directly applying 2.4.17, p. 90. The
    interval includes the infinity endpoint with its
    extended-real order topology. *)
Theorem bounded_probability_exponent_norm_continuous (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (M : R) :
  mu setT = 1 -> (0<M)%R -> (forall x, (`|g x|<=M)%R) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    (measure_exponent_norm mu (partial_function_total g) t : extended_real_line R)).
Proof.
move=> hprob hM hgM hg.
have he : measure_finite_norm_exponents mu (partial_function_total g) =
    [set t : extended_real_line R | 1<=t].
  apply/seteqP; split=> t; first by move=> [ht _].
  move=> ht; split=> //.
  exact: (@bounded_probability_exponent_norm_finite R X mu hm g M t hprob hM hgM ht hg).
have hc : closed [set t : extended_real_line R | 1<=t].
  exact: order_closed_upper_ray_closed.
have hcl : closure [set t : extended_real_line R | 1<=t]=[set t | 1<=t].
  exact: esym ((closure_id _).1 hc).
have hh := @measure_exponent_norm_continuous_on_closure R X mu hm g hg.
by rewrite he hcl in hh.
Qed.
