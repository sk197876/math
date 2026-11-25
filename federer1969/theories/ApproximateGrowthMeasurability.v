(** Federer (1969), 3.1.8, p. 217, first proof
    paragraph: finite approximate growth makes the domain measurable
    and the function measurable for the restricted measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureBasic MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext
  MeasureDensityPoints DensityMeasurableSets MeasureApproximateLimitUP MeasureApproximateOrderLimits
  MeasurableFunctionUP ApproximateMetricGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [everywhere_relative_approximate_continuity_measurable]:
    the use of 2.9.11 and 2.9.13 in Federer 3.1.8,
    p. 217. Approximate continuity is required only at points
    of the actual domain A. The conclusion uses phi restricted
    to A, without claiming that A is conull in the ambient space. *)
Theorem everywhere_relative_approximate_continuity_measurable
    (R : realType) (X : metricType R) (Y : topologicalType)
    (phi : set X->\bar R) (V : X->set X->Prop)
    (A : set X) (f : X->Y) :
  is_measure_derivation_context phi V ->
  (forall a, A a -> is_measure_approximately_continuous_at phi V
    (partial_function_source_restrict A (partial_function_total f)) a) ->
  measure_measurable phi A /\
  is_measure_measurable_function (measure_restrict phi A)
    (partial_function_source_restrict A (partial_function_total f)).
Proof.
move=> hc ha.
pose hm := derivation_measure_law (derivation_context_measure hc).
pose F := partial_function_source_restrict A (partial_function_total f).
have hpre W : open W -> measure_measurable phi (partial_function_preimage F W).
  move=> hW; pose S := partial_function_preimage F W.
  apply: (density_complement_zero_points_conclusions S hc).2.2.2.2.
  apply: (measure_null_subset hm _ (measure_empty hm)).
  move=> x [hx hn].
  have [y [[hAx hxy] hWy]] := hx.
  have [v [hv hl]] := ha x hAx.
  have heq : v=y := partial_function_single_valued hv (conj hAx hxy).
  have hN : nbhs v W.
    rewrite openE in hW; apply: hW; by rewrite heq.
  exact: hn (hl W hN).
have hdomain : partial_function_domain F=A.
  by rewrite /F partial_function_source_restrict_domain partial_function_total_domain setIT.
have hwhole : partial_function_preimage F setT=A.
  apply/seteqP; split=> x.
  - by move=> [y [[hx _] _]].
  - move=> hx; exists (f x); split=> //; by split.
split.
- have hh := hpre setT openT; by rewrite hwhole in hh.
- constructor.
  + rewrite /measure_almost_everywhere hdomain /measure_restrict setICr.
    exact: measure_empty hm.
  + move=> W hW; exact: measure_restrict_measurable (hpre W hW).
Qed.

(** Source for [finite_approximate_growth_measurable]:
    the complete initial inference in the proof of Federer
    3.1.8, p. 217. No measurability assumption is made
    on A or on f before applying the growth hypothesis. *)
Theorem finite_approximate_growth_measurable (R : realType)
    (X Y : metricType R) (phi : set X->\bar R) (V : X->set X->Prop)
    (A : set X) (f : X->Y) :
  is_measure_derivation_context phi V ->
  (forall a, A a -> (measure_approximate_upper_limit phi V
    (partial_metric_growth_quotient A f a) a< +oo)%E) ->
  measure_measurable phi A /\
  is_measure_measurable_function (measure_restrict phi A)
    (partial_function_source_restrict A (partial_function_total f)).
Proof.
move=> hc hg.
apply: (everywhere_relative_approximate_continuity_measurable hc _)=> a ha.
have [M [hM hzero]] := finite_approximate_growth_exception hc (hg a ha).
exact: (growth_exception_approximate_continuity hc ha hM hzero).
Qed.
