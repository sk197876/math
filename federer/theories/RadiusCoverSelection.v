(** Public interface for Federer (1969), Lemma 2.8.10, p. 147. The eligible
    pairs retain centers and positive radii bounded strictly by mu. The
    selected family is used only through its abstract laws; the
    maximal-family proof is hidden. Source context:
    RadiusCoverSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls RadiusCoverSelectionUP RadiusCoverSelectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radius_cover_selection]: the selected
    parameter subset R in Federer 2.8.10, p. 147.
    The selected value is opaque through its sealing module. *)
Definition radius_cover_selection (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :=
  @RadiusCoverSelection.value R X tau mu Q ht hm hQ.

(** Source for [radius_cover_selection_specification]: the
    membership, separation and domination properties in Federer
    2.8.10, p. 147. The domination uses s>r/tau,
    exactly as printed. *)
Theorem radius_cover_selection_specification (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :
  is_radius_cover_selection tau Q (@radius_cover_selection R X tau mu Q ht hm hQ).
Proof. exact: RadiusCoverSelection.laws. Qed.

(** Source for [federer_2_8_10]: direct formalisation of
    the complete lemma in Federer 2.8.10, p. 147:
    for 1<tau, 0<mu and pairs with radii in (0,mu),
    a subset satisfies (1) rho(a,b)>r+s for distinct
    selected pairs and (2) every eligible (a,r) is within
    r+s of a selected (b,s) with s>r/tau. No
    separability, countability or inhabitedness is added. *)
Theorem federer_2_8_10 (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R)) :
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q ->
  exists P, is_radius_cover_selection tau Q P.
Proof.
move=> ht hm hQ; exists (@radius_cover_selection R X tau mu Q ht hm hQ).
exact: radius_cover_selection_specification.
Qed.

(** Source for [radius_selection_balls_disjoint]: supporting
    geometric consequence of condition (1) in Federer
    2.8.10, p. 147, used when passing from parameters
    to balls in 2.8.12, p. 149, after condition (2).
    The triangle inequality
    prevents a point from belonging to two associated balls. *)
Lemma radius_selection_balls_disjoint (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X * R)) :
  is_radius_cover_selection tau Q P -> forall p q,
  P p -> P q -> p <> q ->
  metric_closed_ball p.1 p.2 `&` metric_closed_ball q.1 q.2 = set0.
Proof.
move=> hP p q hp hq hne; apply/seteqP; split=> [x [hpx hqx]|x []].
have hsep := @radius_selection_separated R X tau Q P hP p q hp hq hne.
have hsum : mdist p.1 q.1 <= p.2+q.2.
  apply: le_trans (metric_triangle p.1 x q.1) _.
  apply: lerD hpx _; by rewrite metric_sym.
have hbad := lt_le_trans hsep hsum; by rewrite ltxx in hbad.
Qed.
