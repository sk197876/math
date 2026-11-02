(** Federer (1969), 2.9.18(1), p. 163: the nowhere dense compact
    positive-length target. The topological law below is background for that
    example, not an additional printed theorem of Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_nowhere_dense]: topology background for
    the target T in Federer 2.9.18(1), p. 163.
    A set is nowhere dense when the complement of its
    closure is dense. This is a law-based topological
    property, independent of any Cantor-set construction. *)
Definition is_nowhere_dense (X : topologicalType) (A : set X) := dense (~` closure A).

(** Source for [closed_nowhere_dense_complement]: supporting
    dense-complement property of the compact target in Federer
    2.9.18(1), p. 163. For a closed set,
    the closure appearing in nowhere density is the set itself. *)
Lemma closed_nowhere_dense_complement (X : topologicalType) (A : set X) :
  closed A -> is_nowhere_dense A -> dense (~` A).
Proof. by move=> hA; rewrite /is_nowhere_dense -((closure_id A).1 hA). Qed.

(** Source for [closed_nowhere_dense_nearby_point]: supporting
    choice of the off-target centers S_j in Federer
    2.9.18(1), p. 163. Every positive-radius
    neighborhood of any point contains a point outside the
    closed nowhere dense target. *)
Lemma closed_nowhere_dense_nearby_point (R : realType) (X : metricType R)
    (A : set X) (x : X) (e : R) :
  closed A -> is_nowhere_dense A -> 0<e ->
  exists y, ~ A y /\ mdist x y<e.
Proof.
move=> hA hnd he.
have hdense := closed_nowhere_dense_complement hA hnd.
have hnon : [set y : X | mdist x y<e] !=set0 by exists x; rewrite /= mdistxx.
have [y [hy hn]] := hdense _ hnon (@metric_open_ball_open R X x e).
by exists y; split.
Qed.
