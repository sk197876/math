(** Federer (1969), 2.10.2(1), p. 171, alternative open covering family.
    This supporting metric-neighbourhood construction enlarges any set to an
    open set with diameter increased by at most twice the enlargement
    radius. It is a proof ingredient, not a separate printed assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_thickening]: supporting union
    of positive-radius open balls about A for the open-cover
    alternative of Federer 2.10.2(1), p. 171. *)
Definition metric_open_thickening (R : realType) (X : metricType R)
    (A : set X) (r : R) : set X :=
  \bigcup_(a in A) [set x | mdist a x<r].

(** Source for [metric_open_thickening_open]: supporting
    openness of the enlargement for Federer 2.10.2(1),
    p. 171, by the general topology of metric balls. *)
Lemma metric_open_thickening_open (R : realType) (X : metricType R)
    (A : set X) (r : R) : open (metric_open_thickening A r).
Proof. apply: bigcup_open=> a _; exact: metric_open_ball_open. Qed.

(** Source for [metric_open_thickening_includes]: supporting
    cover containment for Federer 2.10.2(1), p. 171. *)
Lemma metric_open_thickening_includes (R : realType) (X : metricType R)
    (A : set X) (r : R) : 0<r -> A `<=` metric_open_thickening A r.
Proof. move=> hr x hx; exists x=> //; by rewrite /= mdistxx. Qed.

(** Source for [metric_open_thickening_diameter_bound]:
    supporting diameter control for the open-cover equality
    in Federer 2.10.2(1), p. 171. The real bound d
    may be zero and A may be empty. *)
Lemma metric_open_thickening_diameter_bound (R : realType) (X : metricType R)
    (A : set X) (d r : R) : 0<=d -> 0<=r ->
  (extended_metric_diameter A<=d%:E)%E ->
  (extended_metric_diameter (metric_open_thickening A r)<=(d+r+r)%:E)%E.
Proof.
move=> hd hr hdiam; apply: (metric_diameter_least
  (extended_metric_diameter_specification (metric_open_thickening A r))).
- by rewrite lee_fin; lra.
- move=> x y [a ha hax] [b hb hby]; rewrite lee_fin.
  have hab : mdist a b<=d.
    have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification A) ha hb) hdiam.
    by move: hh; rewrite lee_fin.
  have htri := metric_triangle x a y.
  have htri' := metric_triangle a b y.
  rewrite (metric_sym x a) in htri.
  change (is_true (mdist a x<r)) in hax.
  change (is_true (mdist b y<r)) in hby.
  lra.
Qed.
