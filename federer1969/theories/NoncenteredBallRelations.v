(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls CoveringRelationUP CoveringRelationFineness
  CenteredBallRelations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [noncentered_closed_ball_relation]: direct relation V in
    Federer 2.9.16, p. 161, and C1. A positive-radius closed ball contains
    the base point, which need not be its center. *)
Definition noncentered_closed_ball_relation (R : realType) (X : metricType R) :=
  fun (x : X) (S : set X) => exists (a : X) (r : R),
    (0<r)%R /\ S=metric_closed_ball a r /\ S x.

(** Source for [noncentered_closed_balls_covering]: supporting
    covering-relation law for the displayed V in Federer
    2.9.16, p. 161. Membership explicitly includes the
    base point in the selected ball. *)
Lemma noncentered_closed_balls_covering (R : realType) (X : metricType R) :
  is_covering_relation (@noncentered_closed_ball_relation R X).
Proof. by move=> x S [a [r [_ [_ hx]]]]. Qed.

(** Source for [centered_closed_balls_subrelation]: supporting
    inclusion supporting the relation of Federer 2.9.16,
    p. 161: it contains the centered relation of 2.9.15,
    p. 160.
    This is only inclusion of relations, without any inference
    that arbitrary larger relations inherit the Vitali property. *)
Lemma centered_closed_balls_subrelation (R : realType) (X : metricType R) (x : X) (S : set X) :
  centered_closed_ball_relation x S -> noncentered_closed_ball_relation x S.
Proof.
move=> [r [hr hS]]; exists x,r; split=> //; split=> //.
by rewrite hS /metric_closed_ball /= mdistxx; exact: ltW hr.
Qed.

(** Source for [noncentered_closed_balls_fine]: supporting
    everywhere fineness for V in Federer 2.9.16, p. 161.
    The included centered balls already have arbitrarily small
    diameters; no dimension or measure hypothesis is needed. *)
Lemma noncentered_closed_balls_fine (R : realType) (X : metricType R) x :
  covering_relation_fine_at (@noncentered_closed_ball_relation R X) x.
Proof.
apply: (@covering_relation_fine_mono R X (@centered_closed_ball_relation R X)
  (@noncentered_closed_ball_relation R X) x _ (@centered_closed_balls_fine R X x)).
by move=> S; exact: centered_closed_balls_subrelation.
Qed.

(** Source for [noncentered_closed_ball_image]: supporting
    identification of V(X) in Federer 2.9.16, p. 161:
    it is exactly the family of positive-radius closed balls.
    Every such ball contains its center, so no inhabited-space
    hypothesis is added for the empty ambient space. *)
Lemma noncentered_closed_ball_image (R : realType) (X : metricType R) (S : set X) :
  covering_relation_image (@noncentered_closed_ball_relation R X) setT S <->
    exists (a : X) (r : R), (0<r)%R /\ S=metric_closed_ball a r.
Proof.
split; first by move=> [x [_ [a [r [hr [hS _]]]]]]; exists a,r.
move=> [a [r [hr hS]]]; exists a; split=> //; exists a,r; split=> //; split=> //.
by rewrite hS /metric_closed_ball /= mdistxx; exact: ltW hr.
Qed.
