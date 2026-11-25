(** Federer (1969), 4.1.5, p. 350: compact
    continuous vector fields are dense in the original
    vector L1 seminorm. The earlier finite-vector
    density theorem and Radon compact characteristic
    approximation supply the result before smoothing
    turns the approximants into actual tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses VectorDaniellRationalSpan
  FunctionLatticeUP CompactSupportFunctionUP RealIntegralFunctionalUP
  MeasureUP MeasureAlmostBasic PartialFunctionBasic PartialFunctionPreimages MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasureLpMembershipUP RadonMeasureUP
  CompactContinuousVectorFields CompactContinuousVectorSpace CompactContinuousVectorModule CompactContinuousVectorMeasurable
  SeparableVectorLone VectorLoneApproximation CharacteristicVectorLoneDensity RadonCompactCharacteristicApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_vector_lone_dense]:
    density of the original compact continuous
    extension domain in L1, supporting the actual
    test density assertion of Federer 4.1.5,
    p. 350, using 2.5.14 and 2.5.12. *)
Theorem compact_continuous_vector_lone_dense (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (hSep:is_separable_normed_space hNY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (F:(X->R)->R)
    (hF:is_real_integral_functional mu
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) F)
    (f:X->real_norm_metric_space hNY):
  is_measure_lp_function mu 1 (partial_function_total f) ->
  is_vector_lone_approximable NY mu (@compact_continuous_vector_fields R X Y NY hNY) f.
Proof.
move=>hf.
have[D hD]:=@rational_dense_subspace_exists R Y NY hNY hSep.
pose Q:=@compact_continuous_vector_fields R X Y NY hNY.
have hQ:=@compact_continuous_vector_space R X Y NY hNY.
have hM:=@compact_continuous_vector_lattice_module R X Y NY hNY.
have hGA w:Q w ->is_measurable_normed_function mu
    (partial_function_total (w:X->real_norm_metric_space hNY)).
  move=>hw; exact:(@compact_continuous_vector_normed_measurable R X Y NY hNY hSep mu hm hr w hw).
apply:(@characteristic_vector_lone_density R X Y NY hNY mu hm
  (@compactly_supported_continuous_functions R X)
  (@radon_compact_characteristic_approximable R X mu hm hr F hF) D hD Q
  (@vector_function_space_zero R X Y Q hQ)).
- move=>u v hu hv; exact:(@vector_function_space_add R X Y Q hQ u v hu hv).
- exact hGA.
- move=>g y hg hy; exact:(@vector_lattice_module_product R X Y NY hNY
    (@compactly_supported_continuous_functions R X) Q hM g y hg.1).
- exact hf.
Qed.
