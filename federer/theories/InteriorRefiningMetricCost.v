(** Federer (1969), 2.10.20, p. 182, final displayed hypothesis: the cost of
    each generator of diameter at most xi is the infimum of costs of
    generators whose interiors contain it and whose diameters are at most
    delta. These are laws on the indexed family, not an unproved axiom or a
    choice of a neighbouring generator. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_interior_refining_metric_cost]: direct
    indexed form of the final cost-infimum hypothesis
    in 2.10.20, p. 182. Positive xi<delta is a
    separate hypothesis of the printed consequence. *)
Definition is_interior_refining_metric_cost (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R) (xi delta : \bar R) :=
  forall j, extended_metric_diameter (S j)<=xi -> c j=
    extended_real_inf [set b | exists k,
      S j `<=` interior (S k) /\ extended_metric_diameter (S k)<=delta /\ b=c k].
