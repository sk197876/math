(** Private proved existence witness for the auxiliary restricted measure
    supporting Federer (1969), 2.10.24, p. 188. Only the sealing module and
    assumption audit may import this file. Source context and abstract
    specification: WeightedRestrictionMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricLimitUP WeightedMetricLimit
  WeightedRestrictionMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_restriction_measure_exists]: supporting
    existence proof for the auxiliary object in the final
    paragraph of 2.10.24, p. 188. The already sealed
    limiting functional supplies a witness to both abstract
    supremum laws, without additional assumptions or axioms. *)
Theorem weighted_restriction_measure_exists (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  exists nu, is_weighted_restriction_measure S c psi f nu.
Proof.
exists (fun A=>weighted_metric_limit S c psi (weighted_function_restriction f A)).
have hL := weighted_metric_limit_specification S c psi.
constructor.
- move=> A delta lambda hd hl; exact: (@weighted_metric_limit_upper R X J S c psi _ hL _ delta lambda hd hl).
- move=> A b hb; exact: (@weighted_metric_limit_least R X J S c psi _ hL _ b hb).
Qed.
