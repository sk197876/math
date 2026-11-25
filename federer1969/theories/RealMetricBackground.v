(** Federer (1969), 2.2.9, p. 65, the special case X=R. This background
    adapter exposes the standard absolute-value distance through the
    project's metric interface while retaining the existing real order
    topology. Source context: NoIsolatedPoints.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [real_line_metric]: supporting carrier for the
    real-line case of Federer 2.2.9, p. 65. This wrapper
    gives the existing standard topology an explicit metric interface
    without changing the canonical hierarchy of the scalar field. *)
Definition real_line_metric (R : realType) : Type := R.
HB.instance Definition _ (R : realType) :=
  PseudoMetric.copy (real_line_metric R) R^o.
Section RealMetric.
Variable R : realType.
Local Notation M := (real_line_metric R).

(** Source for [real_line_distance_nonnegative]: elementary metric
    background for Federer 2.2.9, p. 65: absolute-value
    distance on the real line is nonnegative. *)
Lemma real_line_distance_nonnegative (x y : M) : 0 <= `|(x : R)-y|.
Proof. exact: normr_ge0. Qed.

(** Source for [real_line_distance_separates]: elementary metric
    background for Federer 2.2.9, p. 65: absolute-value
    distance vanishes only for equal real numbers. *)
Lemma real_line_distance_separates (x y : M) : `|(x : R)-y| = 0 -> x = y.
Proof. by move/eqP; rewrite normr_eq0 subr_eq0=> /eqP. Qed.

(** Source for [real_line_ball_distance]: topology compatibility
    supporting Federer 2.2.9, p. 65: the existing standard
    real balls are exactly the strict absolute-distance balls. *)
Lemma real_line_ball_distance (x : M) d : ball x d = [set y | `|(x : R)-y| < d].
Proof. by []. Qed.

HB.instance Definition _ := PseudoMetric_isMetric.Build R M
  real_line_distance_nonnegative real_line_distance_separates real_line_ball_distance.

(** Source for [real_line_metric_distanceE]: supporting metric
    identity for the real-line case of Federer 2.2.9, p. 65.
    It exposes the standard distance without replacing its topology. *)
Lemma real_line_metric_distanceE (x y : M) : mdist x y = `|(x : R)-y|.
Proof. by []. Qed.
End RealMetric.
