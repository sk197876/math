(** Public weighted cutoff limit for Federer (1969), 2.10.24, p. 187. The
    supremum construction stays sealed; subsequent arguments use only its
    order laws. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import WeightedMetricLimitUP WeightedMetricLimitSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_limit]: direct limit
    of lambda_delta(f) in 2.10.24, p. 187,
    through the sealed supremum interface. *)
Definition weighted_metric_limit (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :=
  @WeightedMetricLimit.value R X J S c psi.

(** Source for [weighted_metric_limit_specification]: the
    public weighted cutoff limit satisfies its
    supremum laws in 2.10.24, p. 187. *)
Lemma weighted_metric_limit_specification (R : realType) (X : metricType R) (J : choiceType)
  (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :
  is_weighted_metric_limit S c psi (weighted_metric_limit S c psi).
Proof. exact: WeightedMetricLimit.laws. Qed.
