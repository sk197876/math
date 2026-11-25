(** Federer 2.8.8, p. 145: the two printed power-growth bounds suffice
    for diametric regularity. Choose the enlargement constant inside the
    proof, then apply 2.8.7 with its original standing hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP CoveringFamilyUP MetricClosedBalls
  DiametricRegularityUP BallPowerGrowth DiametricRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ball_power_growth_regularity_exists]: Federer 2.8.8,
    p. 145, the sufficient estimate at r and (1+2tau)r. The constant lambda
    greater than one is derived; it is not an extra theorem hypothesis. *)
Theorem ball_power_growth_regularity_exists (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : set (set X))
    (n : nat) (u v tau : R) :
  0 < u -> 1 < tau ->
  (forall a r, 0 < r -> F (metric_closed_ball a r) ->
    has_ball_power_growth_bounds mu n u v a r /\
    has_ball_power_growth_bounds mu n u v a ((1+2*tau)*r)) ->
  exists lambda : R, 1 < lambda /\
    is_diametrically_regular_ball_family mu F tau lambda.
Proof.
move=> hu ht hg.
pose q := v*(1+2*tau)^+n/u.
have h2 : (0 < 2 :> R) by rewrite ltr0n.
have h12 : (1 < 2 :> R) by rewrite ltr1n.
have hl : 1 < 2 + `|q|.
  have h := ltr_leD h12 (normr_ge0 q); by rewrite addr0 in h.
have hq : q < 2 + `|q|.
  apply: le_lt_trans (ler_norm q) _.
  have h := ltr_leD h2 (lexx `|q|); by rewrite add0r in h.
exists (2 + `|q|); split=> //.
exact: (@ball_power_growth_diametric_regularity R X mu hm F n u v tau
  (2 + `|q|) hu ht hq hg).
Qed.

(** Source for [ball_power_growth_family_adequate]: Federer 2.8.8,
    p. 145, application of 2.8.7. Under its original context, bounded
    diameter weight and fineness hypotheses, the two growth estimates
    alone supply the needed diametric regularity and yield adequacy. *)
Theorem ball_power_growth_family_adequate (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) (A : set X)
    (d : set X -> R) (n : nat) (u v tau : R) :
  is_covering_theory_context F mu ->
  is_real_diameter_weight F d -> is_positive_closed_ball_family F ->
  (exists C, forall S, F S -> d S <= C) ->
  0 < u -> 1 < tau ->
  (forall a r, 0 < r -> F (metric_closed_ball a r) ->
    has_ball_power_growth_bounds mu n u v a r /\
    has_ball_power_growth_bounds mu n u v a ((1+2*tau)*r)) ->
  family_covers_finely F A -> family_is_measure_adequate mu F A.
Proof.
move=> hc hd hballs hbounded hu ht hg hf.
have [lambda [hl hreg]] := @ball_power_growth_regularity_exists R X mu
  (covering_context_measure hc) F n u v tau hu ht hg.
exact: (@diametrically_regular_family_adequate R X F mu A d tau lambda
  hc hd hballs hbounded ht hl hreg hf).
Qed.
