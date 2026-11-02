(** Federer (1969), 2.10.20, pp. 181–182: a finite positive cutoff
    approximation is the limit of its bounded-ball truncations. The proof
    retains Federer's separated-shell and vanishing-tail argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MetricClosedBalls MetricScaleEnvelopeUP MetricScaleCutoffCost
  MetricScaleSeparation RadialShellMeasureBounds RadialMassSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_radial_continuity]: direct
    radial exhaustion claim in 2.10.20, pp. 181–182,
    for an abstract approximation with the printed
    finite positive cutoff. No measurability or finite
    mass assumption on A is added. *)
Theorem metric_scale_radial_continuity (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R) (delta : R)
    (nu : set X -> \bar R) (A : set X) (a : X) :
  (0<delta)%R -> (forall j, 0<=c j) -> is_metric_scale_envelope S c delta%:E nu ->
  unbounded_radius_order_limit (fun r => nu (A `&` metric_closed_ball a r)) (nu A).
Proof.
move=> hd hc hn.
have hm := metric_scale_envelope_is_measure hn hc.
pose t := (delta+1)%R.
have ht : (0<t)%R by rewrite /t; lra.
have hdt : delta%:E<t%:E by rewrite lte_fin /t; lra.
have hsep : has_uniform_separated_union_bound nu t.
  move=> B C hBC.
  exact: (@metric_scale_envelope_separated_bound R X J S c delta%:E nu B C t hn hc hdt hBC).
have he := @separated_radial_mass_supremum R X nu a A t hm ht hsep.
have hlim := @radial_mass_has_supremum_limit R X nu a A hm.
by rewrite -he in hlim.
Qed.

(** Source for [federer_2_10_20_radial]: printed
    radial equality in 2.10.20, p. 181, as
    an actual extended order limit at r tending to
    infinity, for the original set family F. *)
Theorem federer_2_10_20_radial (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (delta : R)
    (nu : set X -> \bar R) (A : set X) (a : X) :
  (0<delta)%R -> (forall S, F S -> 0<=c S) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta%:E nu ->
  unbounded_radius_order_limit (fun r => nu (A `&` metric_closed_ball a r)) (nu A).
Proof.
move=> hd hc hn; apply: (@metric_scale_radial_continuity R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) delta nu A a hd _ hn)=> j.
exact: hc _ (set_valP j).
Qed.
