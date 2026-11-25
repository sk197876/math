(** Supporting diameter estimates for Federer (1969), 2.10.2(1), p. 171, and
    the nonexpanding case of 2.10.11, p. 176, used for 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_diameter_nonexpanding]: supporting diameter
    comparison in the image-cover proof of Federer 2.10.11, p. 176 This is
    only the distance-nonincreasing case, with no multiplicity assertion. *)
Lemma extended_metric_diameter_nonexpanding (R : realType)
    (X Y : metricType R) (f : X -> Y) :
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  forall A, extended_metric_diameter (f @` A)<=extended_metric_diameter A.
Proof.
move=> hf A; apply: (metric_diameter_least
  (extended_metric_diameter_specification (f @` A))).
- exact: metric_diameter_nonnegative (extended_metric_diameter_specification A).
- move=> _ _ [x hx <-] [y hy <-].
  have h : (mdist (f x) (f y))%:E <= (mdist x y)%:E by rewrite lee_fin; exact: hf.
  exact: le_trans h (metric_diameter_upper (extended_metric_diameter_specification A) hx hy).
Qed.

(** Source for [extended_metric_diameter_singleton]:
    supporting degenerate-cover case of Federer 2.10.2(1),
    p. 171; the diameter of a singleton is zero. *)
Lemma extended_metric_diameter_singleton (R : realType) (X : metricType R) (x : X) :
  extended_metric_diameter [set x]=0.
Proof.
apply/eqP; rewrite eq_le (metric_diameter_nonnegative
  (extended_metric_diameter_specification [set x])) andbT.
apply: (metric_diameter_least (extended_metric_diameter_specification [set x]))=> //.
by move=> _ _ -> ->; rewrite mdistxx.
Qed.
