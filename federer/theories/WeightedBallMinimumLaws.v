(** Federer (1969), 2.10.40, printed pp. 199–200: the least feasible scale c
    equals the infimum of nonnegative scales with nonempty feasible-centre
    set. Derive its order uniqueness and infimum identity from the abstract
    minimum laws before constructing a witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_feasible_scales]: direct
    set whose infimum defines c in 2.10.40,
    p. 199. Only nonnegative real scales are used. *)
Definition weighted_ball_feasible_scales (R : realType) n P : set R :=
  [set t | 0<=t /\ @weighted_ball_centres R n P t !=set0].

(** Source for [weighted_minimum_scale_member]: supporting
    attainment of the scale infimum in 2.10.40,
    pp. 199–200, from the abstract feasibility law. *)
Lemma weighted_minimum_scale_member (R : realType) n P D :
  @is_weighted_ball_minimum R n P D ->
  weighted_ball_feasible_scales P (weighted_minimum_scale D).
Proof.
move=> hD; split; first exact: weighted_minimum_scale_nonnegative_law hD.
exists (weighted_minimum_centre D); exact: weighted_minimum_feasible_law hD.
Qed.

(** Source for [weighted_minimum_scale_unique]: supporting
    uniqueness of the least scale in 2.10.40,
    pp. 199–200. This order argument assumes
    neither uniqueness of centres nor compactness. *)
Lemma weighted_minimum_scale_unique (R : realType) n P D E :
  @is_weighted_ball_minimum R n P D -> is_weighted_ball_minimum P E ->
  weighted_minimum_scale D=weighted_minimum_scale E.
Proof.
move=> hD hE; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@weighted_minimum_least_law R n P D hD (weighted_minimum_scale E)
    (weighted_minimum_centre E) (weighted_minimum_scale_nonnegative_law hE)
    (weighted_minimum_feasible_law hE)).
- exact (@weighted_minimum_least_law R n P E hE (weighted_minimum_scale D)
    (weighted_minimum_centre D) (weighted_minimum_scale_nonnegative_law hD)
    (weighted_minimum_feasible_law hD)).
Qed.

(** Source for [weighted_minimum_scale_infimum]: direct
    c=inf{t:Y_t nonempty} identification in 2.10.40,
    p. 199, from the public order specification.
    This real infimum is the general set-theoretic
    background already used for compact extrema. *)
Theorem weighted_minimum_scale_infimum (R : realType) n P D :
  @is_weighted_ball_minimum R n P D ->
  weighted_minimum_scale D=inf (weighted_ball_feasible_scales P).
Proof.
move=> hD.
have hmember := weighted_minimum_scale_member hD.
have hne : weighted_ball_feasible_scales P !=set0 by exists (weighted_minimum_scale D).
have hl : lbound (weighted_ball_feasible_scales P) (weighted_minimum_scale D).
  move=> t [ht [y hy]]; exact (@weighted_minimum_least_law R n P D hD t y ht hy).
have hhas : has_lbound (weighted_ball_feasible_scales P) by exists (weighted_minimum_scale D).
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: lb_le_inf hne hl.
- exact (@ge_inf R (weighted_ball_feasible_scales P) hhas
    (weighted_minimum_scale D) hmember).
Qed.
