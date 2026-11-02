(** Federer (1969), 2.5.14, p. 108: private assembly of the Radon vector
    representation. Select measurable bounded scalar component densities
    using 2.5.10, construct the weak dual density by the argument of 2.5.12,
    pp. 104–106, and normalize its representative. No unit series, countable
    base of X, or global lattice regularity is assumed. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellRepresentationUP VectorDaniellNormalisationUP MeasureUP RadonMeasureUP
  RealIntegralFunctionalUP BoundedComponentFamilyUP RadonVectorComponentDensity
  RadonVectorDensityMeasurability RadonVectorIntegralFormula RadonVectorUnitNorm
  RadonDualNormalizationConstruction TrivialVectorVariation MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_normalised_vector_density_exists]: the
    vector existence conclusion retained from Federer 2.5.12,
    p. 103, in 2.5.14, p. 108. Local rather than
    global uniqueness is treated separately. Zero-dimensional
    spaces have zero variation measure and require no unit
    functional. The construction is hidden by an opaque seal. *)
Theorem radon_normalised_vector_density_exists (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T)) :
  exists k : X -> weak_dual_space hN, is_normalised_vector_daniell_density phi Q T k.
Proof.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
have hcomp y := @radon_vector_component_density R X E N hN Q T hQ hM hT phi hphi hr hrep y.
pose kk y := projT1 (cid (hcomp y)).
have hkk : is_bounded_component_density_family N (@compactly_supported_continuous_functions R X) T phi kk.
  move=> y; exact: projT2 (cid (hcomp y)).
pose k := @vector_density_point R X E N hN D hD kk.
have hi := @radon_vector_density_integral_formula R X E N hN Q T hQ hM hT phi hphi hrep hr D hD kk hkk.
have hk : is_vector_daniell_density phi Q T k.
  constructor; last exact: hi.
  exact (@radon_vector_density_weak_measurable R X E N hN Q T hQ hM hT phi hphi hr hrep D hD kk hkk).
have hn := @radon_vector_density_norm_measurable R X E N hN Q T hQ hM hT phi hphi hr hrep D hD kk hkk.
case: (pselect (exists y : E, y<>0))=> hE.
- apply: (@radon_dual_normalization_exists R X E N hN phi hphi hr Q T hM k hE hk).
  exact (@represented_radon_vector_density_locally_unit_norm R X E N hN Q T hQ hM hT
    phi hphi hrep hr D hD kk hkk hi).
- have hzero (y : E) : y=0 by apply: contrapT=> hy; apply: hE; exists y.
  have hvar := @trivial_vector_variation_zero R X E N hN
    (@compactly_supported_continuous_functions R X) Q T hQ hT hzero.
  have hmu := @radon_positive_compact_zero_measure R X phi hphi hr
    (variation_integral N Q T) hrep hvar.
  exists k; constructor=> //.
  move=> x; exact: (vector_density_unit_ball hD kk x).2.
Qed.
