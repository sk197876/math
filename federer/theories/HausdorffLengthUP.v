(** Federer (1969), 2.10.2(1), p. 171: the one-dimensional Hausdorff measure
    is the Caratheodory construction using all nonempty subsets and cost
    diam S. This specializes the printed normalization: alpha(1)=2 is stated
    in 2.7.16(1), p. 135. Closed nonempty subsets give the same measure, as
    proved separately. These are the actual Hausdorff-length laws needed by
    the planar example in 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameter CaratheodoryLimitUP CaratheodoryLimitUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [nonempty_metric_sets]: the family of
    all nonempty subsets in Federer 2.10.2(1), p. 171.
    An empty ambient space gives an empty family. *)
Definition nonempty_metric_sets (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type [set A : set X | A !=set0]].

(** Source for [nonempty_closed_metric_sets]: the alternative closed
    nonempty cover family in Federer 2.10.2(1), p. 171 *)
Definition nonempty_closed_metric_sets (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type [set A : set X | closed A /\ A !=set0]].

(** Source for [is_hausdorff_length]: the abstract
    one-dimensional Hausdorff-measure specification of Federer
    2.10.2(1), p. 171. Its covering costs and diameter
    cutoffs are exactly the normalized m=1 formula. *)
Definition is_hausdorff_length (R : realType) (X : metricType R)
    (mu : set X -> \bar R) : Prop :=
  @is_caratheodory_limit R X (@nonempty_metric_sets R X)
    (fun A => val A) (fun A => extended_metric_diameter (val A)) mu.

(** Source for [is_closed_hausdorff_length]: supporting
    specification of the closed-cover alternative in Federer
    2.10.2(1), p. 171. Equivalence with unrestricted
    nonempty covers is a proved theorem, not an imposed axiom. *)
Definition is_closed_hausdorff_length (R : realType) (X : metricType R)
    (mu : set X -> \bar R) : Prop :=
  @is_caratheodory_limit R X (@nonempty_closed_metric_sets R X)
    (fun A => val A) (fun A => extended_metric_diameter (val A)) mu.

(** Source for [hausdorff_length_unique]: the definition
    in Federer 2.10.2(1), p. 171, determines the
    measure uniquely through the covering-infimum laws. *)
Lemma hausdorff_length_unique (R : realType) (X : metricType R)
    (mu rho : set X -> \bar R) :
  is_hausdorff_length mu -> is_hausdorff_length rho -> forall A, mu A=rho A.
Proof. exact: caratheodory_limit_unique. Qed.
