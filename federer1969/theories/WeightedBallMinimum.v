(** Public weighted-ball minimum supporting Federer (1969), 2.10.40, printed
    pp. 199–200. Downstream results use the abstract
    nonnegative-feasible-least laws of the opaque choice. Source context:
    WeightedBallMinimumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric WeightedBallMinimumUP WeightedBallMinimumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_weighted_ball_minimum]: abstract
    chosen centre and scale in 2.10.40,
    pp. 199–200, independent of the private
    nested-intersection witness. *)
Definition compact_weighted_ball_minimum (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (hP : compact P) (hne : P !=set0) (hpos : positive_ball_parameter_family P) :=
  @WeightedBallMinimum.value R n P hP hne hpos.

(** Source for [compact_weighted_ball_minimum_specification]: proved
    abstract minimum laws of 2.10.40, pp. 199–200.
    Uniqueness and contact-hull conclusions are derived
    separately from this specification. *)
Theorem compact_weighted_ball_minimum_specification (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (hP : compact P) (hne : P !=set0) (hpos : positive_ball_parameter_family P) :
  is_weighted_ball_minimum P (@compact_weighted_ball_minimum R n P hP hne hpos).
Proof. exact: WeightedBallMinimum.laws. Qed.
