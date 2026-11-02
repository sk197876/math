(** Federer (1969), 2.5.14, p. 108: the density in the Radon vector theorem
    is only locally almost unique. Scalar local uniqueness on a countable
    dense rational subspace gives a common locally null exceptional set;
    continuity of dual functionals then identifies all coordinates. No
    common bound on competing densities is required. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellUniqueness VectorDaniellDensities
  VectorDaniellRepresentationUP MeasureUP RadonMeasureUP RealIntegralFunctionalUP
  RadonLatticeLocalUniqueness LocallyNullMeasureUP LocallyAlmostMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_vector_density_locally_unique]: the
    explicit local uniqueness qualification in Federer 2.5.14,
    p. 108. Competing densities need only satisfy weak
    measurability and the representation formula; unit-ball or
    normalization laws are not imposed. *)
Theorem radon_vector_density_locally_unique (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (k l : X -> weak_dual_space hN) :
  is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q ->
  is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
    (variation_integral N Q T) ->
  is_vector_daniell_density phi Q T k -> is_vector_daniell_density phi Q T l ->
  measure_locally_almost_everywhere phi [set x | k x=l x].
Proof.
move=> hM hrep hk hl.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
have hy y : D y -> measure_locally_almost_everywhere phi [set x | val (k x) y=val (l x) y].
  move=> _; apply: (@radon_compact_lattice_density_locally_unique R X phi hphi hr
    (variation_integral N Q T) (component_integral T y) _ _ hrep).
  - exact (@vector_daniell_density_component R X E N hN
      (@compactly_supported_continuous_functions R X) Q T phi hphi k hM hk y).
  - exact (@vector_daniell_density_component R X E N hN
      (@compactly_supported_continuous_functions R X) Q T phi hphi l hM hl y).
have hall := measure_locally_almost_countable hphi hD.1 hy.
apply: (measure_locally_almost_mono hphi _ hall)=> x hx.
apply: val_inj; apply: (@dual_space_dense_eq R E N hN D (val (k x)) (val (l x)) hD.2.1).
- exact: set_valP (k x).
- exact: set_valP (l x).
- exact: hx.
Qed.
