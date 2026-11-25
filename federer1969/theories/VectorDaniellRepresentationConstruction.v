(** Federer (1969), 2.5.12, printed pp. 103–106: existence of the normalised
    weakly measurable representing density. This private assembly selects a
    countable dense rational subspace and the scalar densities from 2.5.9,
    then invokes the proved extension, measurability, integral formula, and
    unit-norm results. The local erratum has no correction to pp. 103–106. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP MeasureUP FunctionLatticeUP
  RealIntegralFunctionalUP FunctionLatticeRegularityUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDensities VectorDaniellDualDensity
  VectorDaniellDualExtension VectorDaniellWeakMeasurability
  VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  VectorDaniellIntegralFormula VectorDaniellUnitNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalised_vector_daniell_density_exists]: the
    existence assertion in Federer 2.5.12, p. 103, proved
    on pp. 104–106. Countable measurability of X is
    derived from the lattice unit series, not added as an
    independent hypothesis. The norm and density laws are proved. *)
Theorem normalised_vector_daniell_density_exists (R : realType) (X : choiceType)
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
  exists k : X -> weak_dual_space hN, is_normalised_vector_daniell_density phi Q T k.
Proof.
have hX := @variation_space_countably_measurable R X E N L Q T phi hphi hrep hseries.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
have [kk hkk] := @component_density_family_exists R X E N hN L Q T
  hL hQ hM hT phi hphi hrep hreg hX.
have hi := @vector_density_integral_formula R X E N hN L Q T hL hQ hM hT
  phi hphi hrep hreg hX D hD kk hkk.
exists (@vector_density_point R X E N hN D hD kk); constructor.
- constructor.
  + exact (@vector_density_weak_measurable R X E N hN L Q T hL hQ hM hT phi hphi hrep hreg hX D hD kk hkk).
  + exact: hi.
- exact (@vector_density_norm_measurable R X E N hN L Q T hL hQ hM hT phi hphi hrep hreg hX D hD kk hkk).
- exact (@represented_vector_density_unit_norm R X E N hN L Q T hL hQ hM hT
    phi hphi hrep hreg hX D hD kk hkk hi).
- move=> x; exact (vector_density_unit_ball hD kk x).2.
Qed.
