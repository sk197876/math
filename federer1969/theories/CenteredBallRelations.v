(** The centered-ball relation in Federer (1969), 2.8.18, p. 152, and the
    conversion from diameter fineness to the radius infima in 2.8.15.
    General metric balls can have several radius representations; no
    identity equates their diameter to twice their radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter
  CoveringRelationUP CoveringRelationFineness CenteredBallFineness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_closed_ball_relation]: the displayed
    V in Federer 2.8.18, p. 152. The base point is
    the center and the radius is a finite positive real. *)
Definition centered_closed_ball_relation (R : realType) (X : metricType R) :=
  fun (x : X) (S : set X) => exists r : R, 0 < r /\ S = metric_closed_ball x r.

(** Source for [centered_closed_balls_covering]: the covering
    relation clause for V in Federer 2.8.18, p. 152.
    Positive-radius closed balls contain their centers. *)
Lemma centered_closed_balls_covering (R : realType) (X : metricType R) :
  is_covering_relation (@centered_closed_ball_relation R X).
Proof. move=> x S [r [hr ->]]; rewrite /metric_closed_ball /= mdistxx; exact: ltW hr. Qed.

(** Source for [centered_closed_balls_fine]: the everywhere
    fineness clause for V in Federer 2.8.18, p. 152.
    A radius e/3 gives diameter at most 2e/3, strictly
    below e; only the metric triangle inequality is used. *)
Lemma centered_closed_balls_fine (R : realType) (X : metricType R) x :
  covering_relation_fine_at (@centered_closed_ball_relation R X) x.
Proof.
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
have hr : 0 < e/3 by rewrite divr_gt0 // ltr0n.
exists (metric_closed_ball x (e/3)); split; first by exists (e/3).
have hd : (extended_metric_diameter (metric_closed_ball x (e/3)) <= (e/3+e/3)%:E)%E.
  apply: (metric_diameter_least (extended_metric_diameter_specification _)).
  - rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
  - move=> y z hy hz; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hy hz.
apply: le_lt_trans hd _; rewrite lte_fin -mulrDl ltr_pdivrMr ?ltr0n //.
by rewrite -mulr2n -(mulr_natr e 2) ltr_pM2l // ltr_nat.
Qed.

(** Source for [closed_ball_small_radius_representation]:
    supporting conversion needed for the application of 2.8.15
    in Federer 2.8.18, p. 152. If a centered ball
    has diameter less than t, replacing its radius r by
    min(r,t) leaves the set unchanged. This includes isolated
    points and singleton balls, without assuming diameter=2r. *)
Lemma closed_ball_small_radius_representation (R : realType) (X : metricType R)
    (x : X) (r t : R) :
  0 < r -> 0 < t -> (extended_metric_diameter (metric_closed_ball x r) < t%:E)%E ->
  metric_closed_ball x r = metric_closed_ball x (Num.min r t).
Proof.
move=> hr ht hd; apply/seteqP; split=> y hy.
- rewrite /metric_closed_ball /= le_min; apply/andP; split=> //.
  have hx : metric_closed_ball x r x by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
  have hm := metric_diameter_upper (extended_metric_diameter_specification _) hx hy.
  have h := le_lt_trans hm hd; move: h; rewrite lte_fin; exact: ltW.
- apply: le_trans hy _; by rewrite ge_min lexx.
Qed.

(** Source for [fine_centered_relation_small_radii]: the zero
    centered-radius infimum used in the proof of Federer 2.8.18, p. 152,
    through 2.8.15, p. 150 It follows from small-diameter related sets by
    choosing a smaller radius representation of the same eligible set when
    necessary. *)
Lemma fine_centered_relation_small_radii (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (Z : set X) :
  (forall x S, C x S -> centered_closed_ball_relation x S) ->
  (forall x, Z x -> covering_relation_fine_at C x) ->
  has_arbitrarily_small_centered_balls (covering_relation_image C Z) Z.
Proof.
move=> hC hf x hx e he.
have ht : 0 < e/2 by rewrite divr_gt0 // ltr0n.
have [S [hS hd]] := (covering_relation_fine_iff_small_diameter C x).1 (hf x hx) _ ht.
have [r [hr hEq]] := hC x S hS.
have hrep : S = metric_closed_ball x (Num.min r (e/2)).
  rewrite hEq; apply: closed_ball_small_radius_representation hr ht _; by rewrite -hEq.
exists (Num.min r (e/2)); split.
- apply/andP; split; first by rewrite lt_min hr ht.
  have hte : e/2 < e by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
  apply: le_lt_trans _ hte; by rewrite ge_min lexx orbT.
- exists x; split=> //; by rewrite -hrep.
Qed.
