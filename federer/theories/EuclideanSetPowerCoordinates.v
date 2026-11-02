(** Federer (1969), 2.10.29, p. 195: scalar coordinate membership of finite
    Cartesian powers. These supporting identities expose a one-coordinate
    power and separate a head from its tail, for the orthogonal regrouping
    of two scalar powers. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanSetPowers EuclideanOneCoordinate EuclideanCoordinateSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_set_power_one_membership]: supporting
    one-coordinate base of the rearrangement in
    2.10.29, p. 195. *)
Lemma euclidean_set_power_one_membership (R : realType) (A : set (real_line_metric R))
    (x : inner_metric_space (@euclidean_inner_productP R 1)) :
  euclidean_set_power 1 A x <-> A (euclidean_one_project x).
Proof.
split; first by move=> h; exact: h ord0.
move=> hx i; by rewrite (ord1 i); exact hx.
Qed.

(** Source for [euclidean_set_power_head_tail_membership]: supporting
    coordinate membership split in 2.10.29,
    p. 195. It is a consequence of
    the intrinsic coordinate predicate, without
    choosing a Cartesian-power implementation. *)
Lemma euclidean_set_power_head_tail_membership (R : realType) n (A : set (real_line_metric R))
    (x : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  euclidean_set_power n.+1 A x <->
    euclidean_set_power n A (@coordinate_tail R n x) /\ A (coordinate_head x).
Proof.
split.
- move=> h; split; last exact: h ord0.
  move=> i; rewrite /coordinate_tail ffunE; exact: h (lift ord0 i).
- move=> [ht hh] i; case: (unliftP ord0 i)=> [j ->|->]; last exact hh.
  by move: (ht j); rewrite /coordinate_tail ffunE.
Qed.
