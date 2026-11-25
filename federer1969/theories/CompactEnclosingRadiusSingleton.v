(** Singleton radius supporting the radius-zero alternative and the local
    wrong-centre correction for Federer (1969), 2.10.31, pp. 195–196. Derive
    the value from the exposed containing and least-bound laws, without
    unfolding the maximum witness or the sealed implementation. Source
    context: CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricClosedBalls CompactSetDistanceProfile CompactEnclosingRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_radius_singleton]: supporting
    singleton case of the centred-radius argument
    in 2.10.31, pp. 195–196. The arbitrary
    metric centre also distinguishes the corrected
    centre zero from the printed a on p. 196. *)
Lemma compact_enclosing_radius_singleton (R : realType) (X : metricType R)
    (a x : X) (C : compact_metric_set X) : val C=[set x] ->
  compact_enclosing_radius a C=mdist a x.
Proof.
move=> he; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (compact_enclosing_radius_least a C (mdist_ge0 a x))=> y hy.
  have hyx : y=x by rewrite he in hy.
  by rewrite hyx /metric_closed_ball /=.
- have hx : val C x by rewrite he.
  exact (compact_enclosing_radius_contains a C x hx).
Qed.
