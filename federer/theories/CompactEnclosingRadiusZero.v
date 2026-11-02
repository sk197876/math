(** Radius-zero case supporting Federer (1969), 2.10.31, p. 195: the
    minimising nonempty compact set is the origin singleton when the minimal
    centred radius is zero. The supporting statement works about any metric
    centre. Source context: CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricClosedBalls CompactSetDistanceProfile CompactEnclosingRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_radius_zero_singleton]: direct
    supporting zero-radius implication for the
    first alternative in 2.10.31, p. 195.
    Nonemptiness of C is part of its compact-set
    carrier and ensures that the singleton is present. *)
Lemma compact_enclosing_radius_zero_singleton (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) :
  compact_enclosing_radius a C=0 -> val C=[set a].
Proof.
move=> hr.
have hpoint x : val C x -> x=a.
  move=> hx; have hd := compact_enclosing_radius_contains a C x hx.
  change (is_true (mdist a x<=compact_enclosing_radius a C)) in hd.
  rewrite hr in hd.
  have hz : mdist a x=0 by apply/eqP; rewrite eq_le hd mdist_ge0.
  exact (esym (@mdist_positivity R X a x hz)).
apply/seteqP; split=> x.
- move=> hx; exact: hpoint x hx.
- move=> hx; have [y hy] := (set_valP C).2.
  have he := hpoint y hy; have hx0 : x=a := hx; by rewrite hx0 -he.
Qed.
