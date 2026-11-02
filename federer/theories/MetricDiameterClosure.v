(** Federer (1969), 2.10.2(1), p. 171: replacing cover sets by their
    closures preserves their diameters. It supports Borel regularity of the
    Hausdorff length used in the example of Federer 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_pair_bound_closure]: supporting finite bound argument
    for the closure identity in Federer 2.10.2(1), p. 171. Two applications
    of closedness of metric balls extend the pairwise bound to the closure. *)
Lemma metric_pair_bound_closure (R : realType) (X : metricType R)
    (A : set X) (r : R) :
  (forall x y, A x -> A y -> (mdist x y<=r)%R) ->
  forall x y, closure A x -> closure A y -> (mdist x y<=r)%R.
Proof.
move=> h x y hx hy.
have hyb a : A a -> (mdist a y<=r)%R.
  move=> ha; apply: (@metric_closed_ball_closed R X a r).
  apply: (@closureS X A (metric_closed_ball a r) _ y hy).
  move=> b hb; exact: h a b ha hb.
rewrite metric_sym.
apply: (@metric_closed_ball_closed R X y r).
apply: (@closureS X A (metric_closed_ball y r) _ x hx).
move=> a ha; change (mdist y a<=r)%R.
rewrite metric_sym; exact: hyb a ha.
Qed.

(** Source for [extended_metric_diameter_closure]: the diameter is unchanged
    by closure, supporting the closed-cover version in Federer 2.10.2(1), p.
    171 Unbounded and empty sets are included. *)
Theorem extended_metric_diameter_closure (R : realType) (X : metricType R)
    (A : set X) : extended_metric_diameter (closure A)=extended_metric_diameter A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact: extended_metric_diameter_mono (@subset_closure X A).
have hA := extended_metric_diameter_specification A.
apply: (metric_diameter_least (extended_metric_diameter_specification (closure A))
  (metric_diameter_nonnegative hA)).
move=> x y hx hy.
case he: (extended_metric_diameter A) hA=> [r| |] hA.
- rewrite lee_fin.
  apply: (@metric_pair_bound_closure R X A r _ x y hx hy).
  move=> a b ha hb; have h := metric_diameter_upper hA ha hb.
  by move: h; rewrite lee_fin.
- exact: leey.
- by have := metric_diameter_nonnegative hA.
Qed.
