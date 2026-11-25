(** Federer (1969), 2.10.3, p. 172: compact
    generators give the same measure as unrestricted
    nonempty Euclidean sets. Specify the alternative
    independently before proving the comparison. Source
    editions: ExteriorDiameterUP.v. No equality of the
    preliminary approximations is included in this definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ExteriorMeasureGauge CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [nonempty_compact_metric_sets]: direct
    restricted generator family of Federer 2.10.3,
    p. 172. The underlying nonempty-set convention is
    retained from the initial family on p. 171. *)
Definition nonempty_compact_metric_sets (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type [set A : set X | compact A /\ A !=set0]].

(** Source for [is_compact_exterior_diameter_measure]:
    independent compact-cover Caratheodory specification
    for Federer 2.10.3, p. 172. The actual exterior
    gauge is retained; compactness is a property of
    the generators, not a premise on the target set. *)
Definition is_compact_exterior_diameter_measure (R : realType) (n m : nat)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : @nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => exterior_diameter_cost m (val j)) nu.
