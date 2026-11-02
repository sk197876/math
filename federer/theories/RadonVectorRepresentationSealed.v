(** Opaquely sealed Radon vector density for Federer (1969), 2.5.14, p. 108.
    The signature exposes only a density and its proved laws, with no
    unit-series or lattice-regularity premise. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP MeasureUP FunctionLatticeUP
  RealIntegralFunctionalUP RadonMeasureUP CompactSupportFunctionUP VectorDaniellHypotheses
  VectorDaniellNormalisationUP RadonVectorRepresentationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type RadonVectorRepresentationSignature.
(** Source for [value]: the density k of Federer 2.5.14, p. 108. *)
Parameter value : forall (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T))
    (hr : is_radon_measure phi), X -> weak_dual_space hN.
(** Source for [laws]: the complete normalised density laws,
    Federer 2.5.14, p. 108, proved by the adapted argument of 2.5.12, pp. 104–106. *)
Parameter laws : forall (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T))
    (hr : is_radon_measure phi),
  is_normalised_vector_daniell_density phi Q T (@value R X E N hN hsep Q T hQ hM hT phi hphi hrep hr).
End RadonVectorRepresentationSignature.

Module RadonVectorRepresentation : RadonVectorRepresentationSignature.
(** Source for [value]: private choice from the proved
    existence theorem of Federer 2.5.14, p. 108. *)
Definition value (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T))
    (hr : is_radon_measure phi) : X -> weak_dual_space hN :=
  projT1 (cid (@radon_normalised_vector_density_exists R X E N hN hsep Q T hQ hM hT phi hphi hr hrep)).
(** Source for [laws]: the chosen witness satisfies the
    density laws of Federer 2.5.14, p. 108. *)
Lemma laws (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T))
    (hr : is_radon_measure phi) :
  is_normalised_vector_daniell_density phi Q T (@value R X E N hN hsep Q T hQ hM hT phi hphi hrep hr).
Proof. exact: projT2 (cid (@radon_normalised_vector_density_exists R X E N hN hsep Q T hQ hM hT phi hphi hr hrep)). Qed.
End RadonVectorRepresentation.
