(** Sealed representing density for Federer (1969), 2.5.12, p. 103. Source
    context and representative conventions are recorded in
    VectorDaniellNormalisationUP.v. The signature exposes only a density and
    its proved mathematical laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP MeasureUP FunctionLatticeUP
  RealIntegralFunctionalUP FunctionLatticeRegularityUP VectorDaniellHypotheses
  VectorDaniellNormalisationUP VectorDaniellRepresentationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type VectorDaniellRepresentationSignature.
(** Source for [value]: the density k of Federer 2.5.12, p. 103. *)
Parameter value : forall (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hL : is_function_lattice L) (hseries : has_lattice_unit_series L)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice L)
      (variation_integral N Q T))
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi), X -> weak_dual_space hN.
(** Source for [laws]: the complete normalised density laws,
    Federer 2.5.12, p. 103, proved on pp. 104–106. *)
Parameter laws : forall (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hL : is_function_lattice L) (hseries : has_lattice_unit_series L)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice L)
      (variation_integral N Q T))
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi),
  is_normalised_vector_daniell_density phi Q T (@value R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg).
End VectorDaniellRepresentationSignature.

Module VectorDaniellRepresentation : VectorDaniellRepresentationSignature.
(** Source for [value]: private choice from the proved
    existence theorem of Federer 2.5.12, pp. 104–106. *)
Definition value (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hL : is_function_lattice L) (hseries : has_lattice_unit_series L)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice L)
      (variation_integral N Q T))
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi) : X -> weak_dual_space hN :=
  projT1 (cid (@normalised_vector_daniell_density_exists R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg)).
(** Source for [laws]: the chosen witness satisfies the
    density laws of Federer 2.5.12, p. 103. *)
Lemma laws (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hL : is_function_lattice L) (hseries : has_lattice_unit_series L)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice L)
      (variation_integral N Q T))
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi) :
  is_normalised_vector_daniell_density phi Q T (@value R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg).
Proof. exact: projT2 (cid (@normalised_vector_daniell_density_exists R X E N hN hsep L Q T hL hseries hQ hM hT phi hphi hrep hreg)). Qed.
End VectorDaniellRepresentation.
