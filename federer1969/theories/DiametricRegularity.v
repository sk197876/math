(** Federer (1969), 2.8.8, p. 145: diametric regularity supplies the
    enlargement estimate in 2.8.7. The abstract diameter and ball-family
    laws are used here; no selected implementation is unfolded. Source
    editions: DiametricRegularityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls
  CoveringFamilyUP WeightedEnlargements EnlargementAdequacy
  DiametricRegularityUP DiameterWeightLaws BallEnlargementBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diametric_regularity_enlargement_control]: the implication
    from diametric regularity to the inequality of 2.8.7 in Federer 2.8.8,
    p. 145. Apply measure monotonicity to the ball-enlargement inclusion. *)
Theorem diametric_regularity_enlargement_control (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) (hm : is_measure mu)
    (d : set X -> R) (tau lambda : R) :
  is_real_diameter_weight F d -> is_positive_closed_ball_family F -> (0 <= tau)%R ->
  is_diametrically_regular_ball_family mu F tau lambda ->
  forall S, F S -> mu (weighted_enlargement F d tau S) < lambda%:E * mu S.
Proof.
move=> hd hballs ht hreg S hS.
have [a [r [hr he]]] := hballs S hS.
move: hS; rewrite he=> hB.
apply: le_lt_trans (@measure_mono R X mu hm _ _
  (@diameter_enlargement_ball_bound R X F d tau hd ht a r hB (ltW hr))) _.
exact: hreg a r hr hB.
Qed.

(** Source for [diametrically_regular_family_adequate]:
    application of 2.8.7 with diameter weight in Federer
    2.8.8, p. 145. F consists of positive-radius
    closed balls, covers A finely, and has bounded diameter
    weight. Diametric regularity then yields adequacy. The
    standing context and scalar bounds remain Federer's. *)
Theorem diametrically_regular_family_adequate (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) (A : set X)
    (d : set X -> R) (tau lambda : R) :
  is_covering_theory_context F mu ->
  is_real_diameter_weight F d -> is_positive_closed_ball_family F ->
  (exists C, forall S, F S -> (d S <= C)%R) ->
  (1 < tau)%R -> (1 < lambda)%R ->
  is_diametrically_regular_ball_family mu F tau lambda -> family_covers_finely F A ->
  family_is_measure_adequate mu F A.
Proof.
move=> hc hd hballs hbounded ht hl hreg hf.
have hn := @diameter_weight_nonnegative R X F d hd.
have ht0 : (0 <= tau)%R := ltW (lt_trans ltr01 ht).
have hbound := @diametric_regularity_enlargement_control R X F mu
  (covering_context_measure hc) d tau lambda hd hballs ht0 hreg.
exact (@enlargement_control_adequacy R X F mu d tau lambda A
  hc hn hbounded ht hl hbound hf).
Qed.
