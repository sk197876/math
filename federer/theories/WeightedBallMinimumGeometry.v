(** Federer (1969), 2.10.40, printed pp. 199–200: derive the singleton and
    contact-convex-hull conclusions from the abstract nonnegative, feasible,
    least-scale laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ConvexHull
  WeightedBallMinimumUP WeightedBallMinimumUniqueness WeightedBallContactCompact
  WeightedBallContactNonempty WeightedBallDirectionalContact CompactHullDirectionalCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_minimum_singleton]: direct
    singleton assertion for Y_c in 2.10.40,
    pp. 199–200. Feasibility supplies membership;
    the independently proved parallelogram argument supplies uniqueness. *)
Theorem weighted_ball_minimum_singleton (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n) :
  compact P -> P !=set0 -> positive_ball_parameter_family P -> is_weighted_ball_minimum P D ->
  weighted_ball_centres P (weighted_minimum_scale D)=[set weighted_minimum_centre D].
Proof.
move=> hP hne hpos hD; apply/seteqP; split=> y hy.
- exact (@weighted_ball_minimum_centres_unique R n P D hP hne hpos hD y
    (weighted_minimum_centre D) hy (weighted_minimum_feasible_law hD)).
- by rewrite hy; exact: weighted_minimum_feasible_law hD.
Qed.

(** Source for [weighted_ball_minimum_contact_hull]: direct
    final convex-hull conclusion in 2.10.40,
    pp. 199–200. The actual contact set is
    compact and nonempty; its directional contact property
    rules out separation from the minimum centre.
    Ambient dimension zero and zero scale are retained. *)
Theorem weighted_ball_minimum_contact_hull (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n) :
  compact P -> P !=set0 -> positive_ball_parameter_family P -> is_weighted_ball_minimum P D ->
  convex_hull (weighted_ball_contact_centres P (weighted_minimum_centre D)
    (weighted_minimum_scale D)) (weighted_minimum_centre D).
Proof.
move=> hP hne hpos hD.
apply: compact_hull_directional_criterion.
- exact: weighted_ball_contact_centres_compact hP.
- exact (@weighted_ball_minimum_contacts_nonempty R n P D hP hne hpos hD).
- move=> u hu; exact (@weighted_ball_minimum_directional_contact R n P D u hP hne hpos hD hu).
Qed.
