(** Federer (1969), 2.2.16, p. 71, first proof paragraph: maximal subsets
    A_n of the support whose distinct points have distance greater than 2/n.
    The abstract specification separates strict separation from inclusion
    maximality. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_strictly_separated_metric_set]: direct
    separation condition on A_n in Federer 2.2.16, p. 71,
    with a general radius r replacing 2/n. *)
Definition is_strictly_separated_metric_set (R : realType) (X : metricType R)
    (r : R) (S : set X) : Prop :=
  forall x y, S x -> S y -> x <> y -> r < mdist x y.

(** Source for [is_maximal_separated_subset]: abstract maximality
    of the subsets chosen in Federer 2.2.16, p. 71.
    Maximal means maximal under inclusion among strictly separated
    subsets of the prescribed ambient set, not largest cardinality. *)
Record is_maximal_separated_subset (R : realType) (X : metricType R)
    (A : set X) (r : R) (S : set X) : Prop := {
  separated_subset_inside : S `<=` A;
  separated_subset_separation : is_strictly_separated_metric_set r S;
  separated_subset_maximal : forall T, T `<=` A ->
    is_strictly_separated_metric_set r T -> S `<=` T -> T `<=` S
}.
