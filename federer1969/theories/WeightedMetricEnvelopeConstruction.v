(** Federer (1969), 2.10.24, p. 186: private
    existence proof for the weighted covering infimum,
    using only the project's sealed extended-real
    completeness. An empty admissible family has value
    infinity, as for the ordinary construction. Source
    editions: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_envelope_exists]: existence
    of the infimum in 2.10.24, p. 186.
    The proof does not assume the later equality
    with the upper integral or an attained cover. *)
Theorem weighted_metric_envelope_exists (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R) :
  exists lambda, is_weighted_metric_envelope S c psi delta lambda.
Proof.
exists (fun f=>extended_real_inf [set b | exists G u,
  is_weighted_metric_cover S psi delta f G u /\ b=weighted_generator_cost c G u]).
constructor.
- move=> f G u hG; apply: extended_real_inf_lower; exists G,u; by split.
- move=> f b hb; apply: extended_real_inf_greatest=> a [G [u [hG ->]]]; exact: hb G u hG.
Qed.
