(** Private diameter witness supporting Federer (1969), 2.10.1, p. 170, and
    the Hausdorff-length example in 2.5.10, p. 101. The extended-real
    supremum is already specified and sealed in this project. Source context
    and empty-set convention: MetricDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds MetricDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_diameter_exists]: supporting
    construction of the diameter used by Federer 2.10.1,
    p. 170. Adjoining zero handles the empty set; no
    boundedness hypothesis on the metric space is imposed. *)
Theorem extended_metric_diameter_exists (R : realType) (X : metricType R)
    (A : set X) : exists d, is_extended_metric_diameter A d.
Proof.
pose S := [set r : \bar R | r=0 \/ exists x y, A x /\ A y /\ r=(mdist x y)%:E].
exists (extended_real_sup S); constructor.
- apply: extended_real_sup_upper; by left.
- move=> x y hx hy; apply: extended_real_sup_upper.
  right; exists x,y; by split=> //; split.
- move=> b hb hbound; apply: extended_real_sup_least.
  move=> r [->|[x [y [hx [hy ->]]]]]; first exact hb.
  exact: hbound x y hx hy.
Qed.
