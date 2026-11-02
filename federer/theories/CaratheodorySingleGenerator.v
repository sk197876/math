(** Federer (1969), 2.10.1, p. 170: the approximating measure need not make
    every open set measurable, and the final measure usually does not extend
    the original cost. These supporting one-generator calculations prepare
    explicit examples of both observations. No relevant local Federer
    erratum correction affects these observations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  CaratheodoryLimitUP CaratheodoryMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [single_generator_scale_mass]: supporting exact
    mass calculation for the counterexamples in Federer 2.10.1,
    p. 170. With one generator S of admissible diameter,
    every nonempty subset of S has its prescribed nonnegative
    cost, because every covering family must contain that generator. *)
Lemma single_generator_scale_mass (R : realType) (X : metricType R)
    (S A : set X) (delta c : \bar R) : 0<=c ->
  extended_metric_diameter S<=delta -> A `<=` S -> (exists x, A x) ->
  metric_scale_envelope (fun _ : unit => S) (fun _ => c) delta A=c.
Proof.
move=> hc hd hAS [x hx].
pose nu := metric_scale_envelope (fun _ : unit => S) (fun _ => c) delta.
have hn := metric_scale_envelope_specification (fun _ : unit => S) (fun _ => c) delta.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hcover : A `<=` \bigcup_(j in [set tt]) (fun _ : unit => S) j.
    move=> y hy; exists tt=> //; exact: hAS y hy.
  have hb := @metric_scale_envelope_lower R X [the choiceType of (unit : Type)]
    (fun _ => S) (fun _ => c) delta nu hn A [set tt] (countable1 tt) (fun _ _ => hd) hcover.
  by rewrite nonnegative_sum_singleton in hb.
- apply: (metric_scale_envelope_greatest hn)=> G _ _ hcov.
  have [j hj _] := hcov x hx.
  exact: nonnegative_sum_term hj.
Qed.

(** Source for [single_oversize_generator_scale_mass]: supporting
    no-cover case for the observation in Federer 2.10.1,
    p. 170, that the final measure need not extend the cost.
    If the sole generator is too large, a nonempty target has
    no admissible cover, so its infimum is positive infinity. *)
Lemma single_oversize_generator_scale_mass (R : realType) (X : metricType R)
    (S A : set X) (delta c : \bar R) :
  delta<extended_metric_diameter S -> (exists x, A x) ->
  metric_scale_envelope (fun _ : unit => S) (fun _ => c) delta A=+oo.
Proof.
move=> hd [x hx]; apply/eqP; rewrite eq_le leey /=.
apply: (metric_scale_envelope_greatest
  (metric_scale_envelope_specification (fun _ : unit => S) (fun _ => c) delta))=> G _ hG hcov.
have [j hj _] := hcov x hx.
by have := lt_le_trans hd (hG j hj); rewrite ltxx.
Qed.
