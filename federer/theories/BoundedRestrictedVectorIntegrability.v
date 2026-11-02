(** Federer (1969), 2.9.22, pp. 167–168: the bounded measurable field v has
    vector integrals on finite real intervals. This supporting
    finite-measure restriction lemma uses the proved L1 domain and integral
    laws of 2.4.12, pp. 86–88. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasurableFunctionUP
  RestrictedFunctionMeasurability SeparableTargetNormedMeasurability FiniteMeasureBoundedNorm
  MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_restricted_vector_lone]: supporting
    local L1 membership in Federer 2.9.22, p. 167.
    A bounded measurable map into a separable normed target
    has the full L1 membership required by 2.4.12 after
    restriction to any set of finite measure. No measurability
    of the restricting set is needed for this implication. *)
Lemma bounded_restricted_vector_lone (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (A : set X) (m L : R)
    (v : X -> real_norm_metric_space hN) :
  countable C -> dense C -> mu A=m%:E ->
  is_measure_measurable_function mu (partial_function_total v) ->
  (forall x, N (v x)<=L) ->
  is_measure_lp_function (measure_restrict mu A) 1 (partial_function_total v).
Proof.
move=> hCc hCd hmass hv hb.
have hmA := measure_restrict_is_measure hm A.
have hvA := measurable_function_for_restricted_measure hm A hv.
have hn := @separable_target_measurable_normed R X E N hN C
  (measure_restrict mu A) hmA (partial_function_total v) hCc hCd hvA.
have hmassA : measure_restrict mu A setT=m%:E by rewrite /measure_restrict setIT.
have hbound : measure_almost_everywhere (measure_restrict mu A)
    (partial_function_preimage (partial_function_total v) [set y | N y<=L]).
  apply: (@measure_almost_everywhere_mono R X (measure_restrict mu A) hmA
    setT _ _ (measure_almost_everywhere_true hmA)).
  by move=> x _; exists (v x); split=> //; exact: hb.
exact (@finite_measure_bounded_norm_lp_one R X E N hN (measure_restrict mu A) hmA
  m L (partial_function_total v) hmassA hn hbound).
Qed.

(** Source for [bounded_restricted_vector_integral_exists]:
    supporting actual vector-integral existence in Federer
    2.9.22, pp. 167–168, by 2.4.12, pp. 87–88.
    The Banach completeness hypothesis is used only for the
    existing sealed vector-integral theorem. *)
Lemma bounded_restricted_vector_integral_exists (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (A : set X) (m L : R)
    (v : X -> real_norm_metric_space hN) :
  countable C -> dense C -> mu A=m%:E ->
  is_measure_measurable_function mu (partial_function_total v) ->
  (forall x, N (v x)<=L) ->
  exists y : E, is_measure_vector_integral (measure_restrict mu A) (partial_function_total v) y.
Proof.
move=> hCc hCd hmass hv hb.
have hf := @bounded_restricted_vector_lone R X E N hN C mu hm A m L v hCc hCd hmass hv hb.
have hmA := measure_restrict_is_measure hm A.
exists (measure_vector_integral hY hmA hf).
exact: measure_vector_integral_specification.
Qed.
