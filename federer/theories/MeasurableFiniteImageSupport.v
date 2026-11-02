(** Federer (1969), 2.3.6, p. 77, final paragraph: Z=spt f#(mu restricted to
    A) is closed, separable and carries almost all image mass. This uses
    exactly 2.2.16, pp. 71–72. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic PartialFunctionPreimages MeasureUP
  MeasureRestriction MeasurePushforward PushforwardMeasurableSets MeasurableFunctionUP
  MeasureSupport MetricSubsetBackground FiniteMeasureSupportSeparable UlamMeasureSupport UlamCardinalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_finite_image_support]: direct support
    assertion in Federer 2.3.6, p. 77, final paragraph,
    for a total representative. Measurability of A is not needed
    for this supporting assertion, only finiteness of its measure. *)
Theorem measurable_finite_image_support (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> Y) (A : set X) (D : set Y) :
  is_measure_measurable_function mu (partial_function_total g) -> mu A < +oo ->
  dense D -> is_ulam_set R D ->
  let S := measure_support (measure_pushforward g (measure_restrict mu A)) in
  closed S /\ (exists H : set (metric_subset S), countable H /\ dense H) /\
  mu (A `&` (g @^-1` (~` S))) = 0.
Proof.
move=> hg hfin hd hu S.
pose nu := measure_pushforward g (measure_restrict mu A).
have hn : is_measure nu := measure_pushforward_is_measure g (measure_restrict_is_measure hm A).
have hnf : nu setT < +oo by rewrite /nu /measure_pushforward /measure_restrict preimage_setT setIT.
have hno U : open U -> measure_measurable nu U.
  move=> hU; apply: pushforward_measurable_from_preimage.
  apply: measure_restrict_measurable.
  have hh := @measurable_function_open_preimage R X Y mu (partial_function_total g) hg U hU.
  by rewrite partial_function_total_preimage in hh.
split; first exact: measure_support_closed.
split; first exact: (@finite_measure_support_separable R Y nu hn hnf hno).
exact: (@finite_measure_ulam_dense_support_complement_null R Y nu hn D hnf hno hd hu).
Qed.
