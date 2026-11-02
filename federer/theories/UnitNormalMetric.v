(** Normal-line metric consequences supporting Federer (1969), 2.10.30, p.
    195. Scalar normal lines are retracted isometries, and bounded source
    sets have bounded scalar sections. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  OrthonormalFamilies RealMetricBackground UnitNormalGeometry SteinerSymmetrisationUP
  MetricDiameterUP MetricDiameter CoveringFamilyUP MetricBoundedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Metric.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation E := (inner_metric_space hB).
Variable u : V.
Hypothesis hu : B u u= 1.
Local Notation c := (inner_coordinate hB u).

(** Source for [normal_line_distance]: supporting isometry of scalar
    coordinates on a perpendicular line in 2.10.30, p. 195 *)
Lemma normal_line_distance (y : E) (s t : real_line_metric R) :
  mdist (y+s*:u : E) (y+t*:u : E)=mdist s t.
Proof.
rewrite inner_metric_distanceE real_line_metric_distanceE.
have he : (y+s*:u)-(y+t*:u)=(s-t)*:u.
  by rewrite opprD addrACA subrr add0r scalerBl.
by rewrite he inner_normZ (unit_normal_norm hB hu) mulr1.
Qed.

(** Source for [normal_coordinate_nonexpanding]: supporting scalar
    retraction estimate for the line-length identity of 2.10.30, p. 195 *)
Lemma normal_coordinate_nonexpanding (x y : E) :
  mdist (c x : real_line_metric R) (c y : real_line_metric R)<=mdist x y.
Proof.
rewrite real_line_metric_distanceE inner_metric_distanceE -linearB.
exact (@normal_coordinate_bound R V B hB u hu (x-y)).
Qed.

(** Source for [normal_sections_bounded]: supporting
    bounded scalar sections for the bounded-set
    definition in 2.10.30, p. 195. The
    bound is uniform in the hyperplane foot, and
    includes empty and nonmeasurable source sections. *)
Theorem normal_sections_bounded (S : set E) :
  metric_set_bounded S -> forall y,
  metric_set_bounded (normal_scalar_section u S y).
Proof.
move=> hb y; apply: le_lt_trans _ hb.
apply: (metric_diameter_least (extended_metric_diameter_specification
  (normal_scalar_section u S y))).
- exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
- move=> s t hs ht; rewrite -(normal_line_distance y s t).
  exact (@metric_diameter_upper R E S (extended_metric_diameter S)
    (extended_metric_diameter_specification S) (y+s*:u) (y+t*:u) hs ht).
Qed.
End Metric.
