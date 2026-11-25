(** Federer (1969), 2.10.41, printed p. 200: apply the weighted minimum-ball
    lemma with P=S times the singleton {1}. These elementary adapters expose
    exactly that parameter family, its compactness, containing-ball
    constraints and contact centres. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_radius_parameters]: direct parameter
    family P=S times {1} in 2.10.41, p. 200.
    This is a predicate specifying the family; it
    makes no choice of a minimum centre. *)
Definition unit_radius_parameters (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
    set ((inner_metric_space (@euclidean_inner_productP R n))*R^o) := S `*` [set 1].

(** Source for [unit_radius_parameters_compact]: supporting
    compactness of P=S times {1} in 2.10.41,
    p. 200, by the elementary finite product theorem. *)
Lemma unit_radius_parameters_compact (R : realType) n S :
  compact S -> compact (@unit_radius_parameters R n S).
Proof. move=> hS; apply: compact_setX hS _; exact: compact_set1. Qed.

(** Source for [unit_radius_parameters_nonempty]: supporting
    nonemptiness requirement in the application of 2.10.40
    inside 2.10.41, p. 200. *)
Lemma unit_radius_parameters_nonempty (R : realType) n S :
  S !=set0 -> @unit_radius_parameters R n S !=set0.
Proof. move=> [a ha]; exists (a,1); by split. Qed.

(** Source for [unit_radius_parameters_positive]: supporting
    positive-radius requirement in the application of
    2.10.40 inside 2.10.41, p. 200. *)
Lemma unit_radius_parameters_positive (R : realType) n S :
  positive_ball_parameter_family (@unit_radius_parameters R n S).
Proof. move=> [a r] [ha ->]; exact: ltr01. Qed.

(** Source for [unit_radius_feasible_centres]: direct equivalence S
    contained in B(b,t) if and only if b belongs to Y_t in 2.10.41, p. 200 *)
Lemma unit_radius_feasible_centres (R : realType) n S (t : R)
    (b : inner_metric_space (@euclidean_inner_productP R n)) :
  weighted_ball_centres (unit_radius_parameters S) t b <-> S `<=` metric_closed_ball b t.
Proof.
split.
- move=> hb a ha; have hh := hb (a,1) (conj ha erefl).
  change (is_true (inner_norm (@euclidean_inner_productP R n) (b-a)<=t)).
  by move: hh; rewrite mul1r.
- move=> hb [a r] [ha ->] /=; rewrite mul1r.
  exact: hb a ha.
Qed.

(** Source for [unit_radius_contact_centres]: direct
    contact family A=S intersect {a:|a-b|=c} used
    in 2.10.41, p. 200. The norm is written
    |b-a|, as in 2.10.40; symmetry makes them equal. *)
Lemma unit_radius_contact_centres (R : realType) n S
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :
  weighted_ball_contact_centres (unit_radius_parameters S) b c=
    S `&` [set a | inner_norm (@euclidean_inner_productP R n) (b-a)=c].
Proof.
apply/seteqP; split=> a.
- move=> [r [[ha hr] hh]].
  change (r= 1) in hr; rewrite hr mul1r in hh; by split.
- move=> [ha hh]; exists 1; split; first by split.
  by rewrite mul1r.
Qed.
