(** Federer (1969), 2.5.14, p. 108, vector paragraph: the variation integral
    of 2.5.12 has a Radon representing measure when L=K(X), without the
    unit-series hypothesis (3). This proves existence of the variation
    measure; construction of its weakly measurable dual density is a
    separate step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportFunctionLattice OrderBoundedVectorFunctionalUP CompactSupportVectorContinuity
  VectorDaniellHypotheses VectorDaniellVariationIntegral CompactPositiveConeExtension
  CompactSupportRadonRepresentation MeasureUP RadonMeasureUP RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_vector_variation_radon_measure]: the
    scalar measure required by the vector generalization in
    Federer 2.5.14, p. 108, obtained from the preceding
    scalar Radon theorem, pp. 107–108. Neither a countable
    base nor a unit series is assumed. Sequential continuity
    is proved from compactness and finite order bounds. *)
Theorem compact_vector_variation_radon_measure (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_vector_function_space Q ->
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T ->
  exists phi : set X -> \bar R, is_measure phi /\ is_radon_measure phi /\
    is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (VectorDaniellHypotheses.variation_integral N Q T).
Proof.
move=> hh hl hQ hM hT.
pose L := @compactly_supported_continuous_functions R X.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hV := @compact_support_vector_variation_functional R X E N hN Q T hh hl hQ hM hT.
have hpos f : positive_function_lattice L f -> 0<=VectorDaniellHypotheses.variation_integral N Q T f.
  move=> hf.
  have hz : function_le (fun _ : X => N (0 : E)) f.
    by move=> x; rewrite (real_seminorm_zero hN.1); exact: hf.2.
  have hb := @variation_integral_upper R X E N hN L Q T hQ hV f (fun _ => 0)
    hf (vector_function_space_zero hQ) hz.
  by rewrite (@variation_zero_map R X E N L Q T hQ hV) in hb.
have [A [hA he]] := @compact_positive_cone_extension R X (VectorDaniellHypotheses.variation_integral N Q T)
  hh hl (@variation_integral_add R X E N hN L Q T hL hQ hM hV)
  (@variation_integral_scale R X E N hN L Q T hL hQ hV)
  hpos.
have [phi [hm [hr hrep]]] := @compact_support_radon_representation R X A hh hl hA.
exists phi; split=> //; split=> // f hf.
rewrite -(he f hf); exact: hrep f hf.1.
Qed.
