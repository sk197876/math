(** Federer (1969), 2.10.40, printed pp. 199–200: the complete weighted
    minimum-ball lemma, including the infimum identity, unique centre and
    contact hull. A real scale is finite by its type. The chosen witness is
    opaque and exposes only its proved order laws. The working erratum has
    no entry for book pp. 199–200. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ConvexHull WeightedBallMinimumUP
  WeightedBallMinimumLaws WeightedBallMinimum WeightedBallMinimumGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_40]: direct complete lemma
    in 2.10.40, pp. 199–200: the infimum
    of feasible nonnegative scales is a finite minimum,
    its feasible-centre set is a singleton, and that
    centre belongs to the convex hull of the contact centres. *)
Theorem federer_2_10_40 (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o)) :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  exists (c : R) (b : inner_metric_space (@euclidean_inner_productP R n)),
    0<=c /\ c=inf (weighted_ball_feasible_scales P) /\ weighted_ball_centres P c=[set b] /\
    convex_hull (weighted_ball_contact_centres P b c) b.
Proof.
move=> hP hne hpos.
pose D := @compact_weighted_ball_minimum R n P hP hne hpos.
have hD := @compact_weighted_ball_minimum_specification R n P hP hne hpos.
exists (weighted_minimum_scale D),(weighted_minimum_centre D).
split; first exact: weighted_minimum_scale_nonnegative_law hD.
split; first exact: weighted_minimum_scale_infimum hD.
split; first exact (@weighted_ball_minimum_singleton R n P D hP hne hpos hD).
exact (@weighted_ball_minimum_contact_hull R n P D hP hne hpos hD).
Qed.
