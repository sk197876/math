(** Federer (1969), 2.10.41, printed p. 200: specialise the order laws for
    weighted balls at unit radii, retaining an abstract minimum-ball
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric WeightedBallMinimumUP
  WeightedBallMinimumUniqueness EuclideanUnitRadiusParameters EuclideanMinimumBallUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_radius_minimum_ball_laws]: direct
    substitution P=S times {1} in 2.10.41, p. 200.
    The minimum-ball laws follow from the weighted
    scale laws, with no private witness computation. *)
Lemma unit_radius_minimum_ball_laws (R : realType) n S D :
  @is_weighted_ball_minimum R n (unit_radius_parameters S) D ->
  is_minimum_enclosing_ball S (weighted_minimum_centre D) (weighted_minimum_scale D).
Proof.
move=> hD; constructor.
- exact: weighted_minimum_scale_nonnegative_law hD.
- exact: (proj1 (unit_radius_feasible_centres _ _ _) (weighted_minimum_feasible_law hD)).
- move=> z t ht hcover.
  exact (@weighted_minimum_least_law R n (unit_radius_parameters S) D hD t z ht
    (proj2 (unit_radius_feasible_centres _ _ _) hcover)).
Qed.

(** Source for [minimum_ball_weighted_laws]: supporting
    converse order-law adapter for 2.10.41, p. 200.
    This builds only the already specified data pair;
    it does not choose a minimum centre. *)
Lemma minimum_ball_weighted_laws (R : realType) n S b r :
  @is_minimum_enclosing_ball R n S b r ->
  is_weighted_ball_minimum (unit_radius_parameters S)
    {| weighted_minimum_centre := b; weighted_minimum_scale := r |}.
Proof.
move=> hD; constructor.
- exact: minimum_ball_radius_nonnegative_law hD.
- exact: (proj2 (unit_radius_feasible_centres _ _ _) (minimum_ball_contains_law hD)).
- move=> t z ht hz.
  exact (@minimum_ball_radius_least_law R n S b r hD z t ht
    (proj1 (unit_radius_feasible_centres _ _ _) hz)).
Qed.

(** Source for [minimum_enclosing_ball_unique]: direct
    unique minimum-ball conclusion of 2.10.41, p. 200,
    for a compact nonempty source. Radii agree by
    leastness; centres agree by 2.10.40's proved
    midpoint argument. Zero radius and dimension zero remain allowed. *)
Theorem minimum_enclosing_ball_unique (R : realType) n S b r b' r' :
  compact S -> S !=set0 -> @is_minimum_enclosing_ball R n S b r ->
  is_minimum_enclosing_ball S b' r' -> b=b' /\ r=r'.
Proof.
move=> hS hne hD hE.
have hrr : r=r'.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact (@minimum_ball_radius_least_law R n S b r hD b' r'
      (minimum_ball_radius_nonnegative_law hE) (minimum_ball_contains_law hE)).
  - exact (@minimum_ball_radius_least_law R n S b' r' hE b r
      (minimum_ball_radius_nonnegative_law hD) (minimum_ball_contains_law hD)).
split=> //.
have hDw := minimum_ball_weighted_laws hD.
apply: (@weighted_ball_minimum_centres_unique R n (unit_radius_parameters S)
  {| weighted_minimum_centre := b; weighted_minimum_scale := r |}
  (unit_radius_parameters_compact hS) (unit_radius_parameters_nonempty hne)
  (@unit_radius_parameters_positive R n S) hDw b b').
- exact: (proj2 (unit_radius_feasible_centres _ _ _) (minimum_ball_contains_law hD)).
- have hc := minimum_ball_contains_law hE; rewrite -hrr in hc.
  exact: (proj2 (unit_radius_feasible_centres _ _ _) hc).
Qed.
