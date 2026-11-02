(** Federer (1969), 2.5.20, p. 114: apply 2.5.12 to E=K(Y), Q=C(X,E), and
    T=mu o S. This verifies the hypotheses and produces the same regular
    variation measure, then proves it Radon using the countable base of
    compact metric X. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionSeparability
  CompactProductVectorFunctional ContinuousVectorFamily CompactMetricSeparability
  CompactPositiveRepresentationRadon CompactSupportVectorContinuity
  CompactSupportFunctionUP CompactSupportFunctionLattice SubtypeCompactHausdorff
  DaniellIntegralUP VectorDaniellHypotheses VectorDaniellRepresentation
  VectorDaniellNormalisationUP MeasureUP RadonMeasureUP RealIntegralFunctionalUP
  FunctionLatticeUP FunctionLatticeRegularityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_vector_representation]: the
    application of 2.5.12 giving the Radon variation measure
    and dual density in Federer 2.5.20, p. 114. This
    intermediate statement precedes the identification of the
    dual values with Daniell integrals. No disintegration is
    assumed as a hypothesis. *)
Theorem compact_product_vector_representation (R : realType) (X Y : metricType R)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (mu : ((X*Y) -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  exists phi : set X -> \bar R, exists k : X -> weak_dual_space (compact_function_norm_laws hE),
    is_measure phi /\ is_radon_measure phi /\
    is_real_integral_functional phi
      (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral (compact_function_norm ev)
        (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
        (compact_product_vector_functional ev mu)) /\
    is_function_lattice_regular
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) phi /\
    is_normalised_vector_daniell_density phi
      (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
      (compact_product_vector_functional ev mu) k.
Proof.
move=> hX hY hmu.
have hsep := compact_metric_function_space_separable hE hY.
have hQ := @continuous_normed_functions_vector_space R X E _ (compact_function_norm_laws hE).
have hM := @continuous_normed_functions_compact_module R X E _ (compact_function_norm_laws hE) hX.
have hT := compact_product_vector_functional_order_bounded hE hX hY hmu.
have hV := compact_support_vector_variation_functional
  (@metric_hausdorff R X) (compact_space_locally_compact hX) hQ hM hT.
have [phi [k [hm [hrep [hr hk]]]]] := @vector_variation_representation R X E _
  (compact_function_norm_laws hE) hsep (@compactly_supported_continuous_functions R X)
  (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
  (compact_product_vector_functional ev mu)
  (@compactly_supported_continuous_functions_lattice R X)
  (@compact_function_lattice_unit_series R X hX) hQ hM hV.
have [B hB] := compact_metric_countable_open_base hX.
have hRad := compact_positive_regular_representation_radon hm (@metric_hausdorff R X) hX hB hrep hr.
exists phi,k; by split=> //; split=> //; split=> //; split.
Qed.
