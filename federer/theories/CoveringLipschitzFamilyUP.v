(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_covering_lipschitz_family]: supporting abstract
    specification of the uniformly one-Lipschitz local averages in Federer
    2.9.9, p. 157 The family has a common partial domain on sufficiently
    small cells, finite values, and a one-Lipschitz bound in its target
    parameter. These are laws to prove, not additional global assumptions. *)
Record is_covering_lipschitz_family (R : realType) (X Y : metricType R)
    (V : X -> set X -> Prop) (u : Y -> partial_function (set X) (\bar R))
    (cap : R) : Prop := {
  (** Source for [covering_family_common_domain]: supporting common domain of
    the positive finite cell means in Federer 2.9.9, p. 157 *)
  covering_family_common_domain : forall x S, V x S -> extended_metric_diameter S<cap%:E ->
    forall y z, partial_function_domain (u y) S -> partial_function_domain (u z) S;
  (** Source for [covering_family_finite]: supporting finite-value
    qualification of the local averages in Federer 2.9.9, p. 157 *)
  covering_family_finite : forall x S, V x S -> extended_metric_diameter S<cap%:E ->
    forall y a, partial_function_graph (u y) S a -> a \is a fin_num;
  (** Source for [covering_family_lipschitz]: supporting uniform Lipschitz
    estimate for the closedness assertion in Federer 2.9.9, p. 157 *)
  covering_family_lipschitz : forall x S, V x S -> extended_metric_diameter S<cap%:E ->
    forall y z (a b : R), partial_function_graph (u y) S a%:E ->
      partial_function_graph (u z) S b%:E -> (`|a-b|<=mdist y z)%R
}.
