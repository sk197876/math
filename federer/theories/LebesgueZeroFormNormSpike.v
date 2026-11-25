(** Federer (1969), 4.1.19, p. 377: a
    private supporting representative test on the
    original positive-dimensional Lebesgue measure.
    The same bounded measurable zero-form has
    zero essential comass, literal global comass one,
    and zero integral against every multivector field. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ApproximateDifferentialAffine PartialFunctionBasic
  MeasurableNormedFunctionUP MeasureEssentialNorm MeasureIntegralUP
  SummableRealFunctionUP CurrentGlobalComassSealed NullSpikeZeroForm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_zero_form_norm_spike]: the
    almost-equality convention in 2.3.1, p. 72,
    and literal global comass in 4.1.7, p. 358,
    give distinct values on this actual form.
    This supports the representative review of
    4.1.19, p. 377; no cochain norm identity
    is assumed in this test. *)
Theorem lebesgue_zero_form_norm_spike (R : realType)
    (h2 : (1+1:R)!=0) :
  exists phi : R_n R 1%N -> A_m (R_n R 1%N) R^o 0%N,
    is_measurable_normed_function (@euclidean_lebesgue_measure R 1%N)
      (partial_function_total
        (fun x => (phi x : real_norm_metric_space
          (@current_form_comass_real_norm R h2 1%N 0%N)))) /\
    measure_essential_norm (@euclidean_lebesgue_measure R 1%N)
      (@current_form_comass R h2 1%N 0%N)
      (partial_function_total phi) = 0%E /\
    @CurrentGlobalComass.value R h2 1%N 0%N setT phi = 1%:E /\
    forall xi : R_n R 1%N -> exterior_power (R_n R 1%N) 0%N,
      is_measure_integral (@euclidean_lebesgue_measure R 1%N)
        (real_total_integrand (fun x => pairing (xi x) (phi x))) 0%E.
Proof.
pose X := R_n R 1%N.
pose a : X := 0.
pose mu := @euclidean_lebesgue_measure R 1%N.
have hm := @euclidean_lebesgue_is_measure R 1%N.
have hNull : mu [set a] = 0%E := @positive_euclidean_singleton_null R 0%N a.
exists (@null_spike_zero_form R 1%N a).
split.
- exact: (@null_spike_zero_form_measurable R h2 1%N a mu hm hNull).
- split.
  + exact: (@null_spike_zero_form_essential_comass R h2 1%N a mu hm hNull).
  + split.
    * exact: (@null_spike_zero_form_global_comass R h2 1%N a).
    * exact: (@null_spike_zero_form_pairing_integral R 1%N a mu hm hNull).
Qed.
