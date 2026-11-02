(** Federer (1969), 2.5.14, p. 108: the rational component argument of
    2.5.12, p. 104, now has a locally null exceptional set. Countability
    concerns only the dense rational subspace and rational coefficients; the
    ambient space need not be countably measurable. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellDensities VectorDaniellDualDensity
  MeasureUP RadonMeasureUP RealIntegralFunctionalUP BoundedComponentFamilyUP
  MeasurableComponentCombination RadonLatticeLocalUniqueness
  LocallyNullMeasureUP LocallyAlmostMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_component_good_set_locally_almost]: local
    rational linearity and the norm bound required for the
    dual extension in Federer 2.5.14, p. 108, by the
    countable argument of 2.5.12, p. 104. *)
Theorem radon_component_good_set_locally_almost (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (VectorDaniellHypotheses.variation_integral N Q T))
    (D : set E) (hD : countable D) (kk : E -> X -> R) :
  is_bounded_component_density_family N (@compactly_supported_continuous_functions R X) T phi kk ->
  measure_locally_almost_everywhere phi (density_good_set N D kk).
Proof.
move=> hkk.
pose L := @compactly_supported_continuous_functions R X.
pose J := D `*` D `*` [set: rat] `*` [set: rat].
pose P (j : E * E * rat * rat) := [set x | kk (ratr j.1.2 *: j.1.1.1+ratr j.2 *: j.1.1.2) x
  =ratr j.1.2*kk j.1.1.1 x+ratr j.2*kk j.1.1.2 x].
have hJ : countable J := countableX (countableX (countableX hD hD) (countableP _)) (countableP _).
have ha j : J j -> measure_locally_almost_everywhere phi (P j).
  case: j=> [[[y z] r] s] _.
  have hc := @measurable_component_density_combination R X E N hN L Q T hQ hM hT phi hphi
    (ratr r) (ratr s) y z (kk y) (kk z) (hkk y).1 (hkk z).1.
  exact: (@radon_compact_lattice_density_locally_unique R X phi hphi hr
    (VectorDaniellHypotheses.variation_integral N Q T) _ _ _ hrep
    (hkk (ratr r *: y+ratr s *: z)).1 hc).
have hall := measure_locally_almost_countable hphi hJ ha.
apply: (measure_locally_almost_mono hphi _ hall)=> x hx y z r s hy hz.
split; last exact: (hkk y).2 x.
exact: hx (((y,z),r),s) (conj (conj (conj hy hz) I) I).
Qed.
