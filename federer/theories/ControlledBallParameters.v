(** Federer (1969), 2.8.9, p. 146, final note: distinct parameters in a
    controlled family have distinct centers and distinct associated closed
    balls. This module uses Federer's strict convention from
    DirectionalLimitationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls DirectionalLimitationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [parameter_closed_ball]: the associated family {B(a,r):(a,r)
    in P} in Federer 2.8.9, p. 146 It retains the given parameter rather
    than choosing a center or radius for an already given subset. *)
Definition parameter_closed_ball (R : realType) (X : metricType R)
    (p : X * R) := metric_closed_ball p.1 p.2.

(** Source for [controlled_centers_injective]: the conclusion a<>b for
    distinct controlled parameters in Federer 2.8.9, p. 146, final note
    Positive radii and the strict center-distance comparison exclude equal
    centers. *)
Lemma controlled_centers_injective (R : realType) (X : metricType R)
    (tau : R) (P : set (X * R)) :
  is_controlled_ball_family tau P -> forall p q,
  P p -> P q -> p.1 = q.1 -> p = q.
Proof.
move=> hP p q hp hq he.
case: (pselect (p=q))=> [heq|hne]; first exact heq.
have hz : mdist p.1 q.1 = 0 by rewrite he mdistxx.
have hposp := @controlled_positive_radii R X tau P hP p hp.
have hposq := @controlled_positive_radii R X tau P hP q hq.
have [[hbig _]|[hbig _]] := @controlled_pair_alternative R X tau P hP p q hp hq hne.
- have hbad := lt_trans hposp hbig; by rewrite hz ltxx in hbad.
- have hbad := lt_trans hposq hbig; by rewrite hz ltxx in hbad.
Qed.

(** Source for [controlled_associated_balls_injective]: B(a,r)<>B(b,s) for
    distinct controlled parameters in Federer 2.8.9, p. 146, final note At
    least one center lies outside the other closed ball. No uniqueness of
    centers or radii is asserted for general balls. *)
Lemma controlled_associated_balls_injective (R : realType) (X : metricType R)
    (tau : R) (P : set (X * R)) :
  is_controlled_ball_family tau P -> forall p q,
  P p -> P q -> parameter_closed_ball p = parameter_closed_ball q -> p = q.
Proof.
move=> hP p q hp hq he.
case: (pselect (p=q))=> [heq|hne]; first exact heq.
have hposp := @controlled_positive_radii R X tau P hP p hp.
have hposq := @controlled_positive_radii R X tau P hP q hq.
have hpcenter : parameter_closed_ball p p.1.
  by rewrite /parameter_closed_ball /metric_closed_ball /= mdistxx ltW.
have hqcenter : parameter_closed_ball q q.1.
  by rewrite /parameter_closed_ball /metric_closed_ball /= mdistxx ltW.
have [[hbig _]|[hbig _]] := @controlled_pair_alternative R X tau P hP p q hp hq hne.
- have hqin : parameter_closed_ball p q.1 by rewrite he.
  have hbad := lt_le_trans hbig hqin; by rewrite ltxx in hbad.
- have hpin : parameter_closed_ball q p.1 by rewrite -he.
  rewrite /parameter_closed_ball /metric_closed_ball /= metric_sym in hpin.
  have hbad := lt_le_trans hbig hpin; by rewrite ltxx in hbad.
Qed.
