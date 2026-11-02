(** Opaque minimum witness for Federer (1969), 2.10.40, printed pp. 199–200.
    Expose only centre and scale data with the proved
    nonnegative-feasible-least laws. Neither uniqueness nor the contact-hull
    conclusion is part of the assumed interface. Source context:
    WeightedBallMinimumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric WeightedBallMinimumUP WeightedBallMinimumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type WEIGHTED_BALL_MINIMUM.
(** Source for [value]: abstract selected centre and
    least feasible scale of 2.10.40, pp. 199–200. *)
Parameter value : forall (R : realType) n
  (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o)),
  compact P -> P !=set0 -> positive_ball_parameter_family P -> weighted_ball_minimum_data R n.
(** Source for [laws]: abstract nonnegative scale,
    feasibility and leastness laws for 2.10.40,
    pp. 199–200. Existence is already proved. *)
Parameter laws : forall (R : realType) n
  (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
  (hP : compact P) (hne : P !=set0) (hpos : positive_ball_parameter_family P),
  is_weighted_ball_minimum P (@value R n P hP hne hpos).
End WEIGHTED_BALL_MINIMUM.
Module WeightedBallMinimum : WEIGHTED_BALL_MINIMUM.
(** Source for [value]: privately proved minimum
    witness supporting 2.10.40, pp. 199–200,
    hidden by opaque module ascription. *)
Definition value (R : realType) n
  (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
  (hP : compact P) (hne : P !=set0) (hpos : positive_ball_parameter_family P) :=
  projT1 (cid (@weighted_ball_minimum_exists R n P hP hne hpos)).
(** Source for [laws]: proved minimum laws supporting
    2.10.40, pp. 199–200, with no exposed
    infimum or centre implementation. *)
Lemma laws (R : realType) n
  (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
  (hP : compact P) (hne : P !=set0) (hpos : positive_ball_parameter_family P) :
  is_weighted_ball_minimum P (@value R n P hP hne hpos).
Proof. exact: (projT2 (cid (@weighted_ball_minimum_exists R n P hP hne hpos))). Qed.
End WeightedBallMinimum.
