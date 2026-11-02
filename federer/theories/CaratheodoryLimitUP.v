(** Federer (1969), 2.10.1, p. 170: the final measure is the supremum of the
    size-delta approximations for positive delta. The specification
    quantifies over every approximation satisfying the covering laws, so it
    does not depend on a particular infimum implementation. This
    construction supports the Hausdorff-length example in Federer 2.5.10, p.
    101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_caratheodory_limit]: abstract supremum laws
    for the displayed definition of the final measure in
    Federer 2.10.1, p. 170. Both finite positive cutoffs
    and infinity are admitted, as in the book. *)
Record is_caratheodory_limit (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) : Prop := {
  (** Source for [caratheodory_limit_upper]: every positive
      scale approximation is below the supremum in
      Federer 2.10.1, p. 170. *)
  caratheodory_limit_upper : forall A delta nu, 0<delta ->
    is_metric_scale_envelope S cost delta nu -> nu A<=mu A;
  (** Source for [caratheodory_limit_least]: least upper
      bound clause in the supremum defining the final
      measure, Federer 2.10.1, p. 170. *)
  caratheodory_limit_least : forall A b,
    (forall delta nu, 0<delta -> is_metric_scale_envelope S cost delta nu -> nu A<=b) ->
    mu A<=b
}.
