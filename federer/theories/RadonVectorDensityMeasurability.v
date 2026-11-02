(** Federer (1969), 2.5.14, p. 108: the Radon dual density is weakly
    measurable. The component construction and countable weak-base argument
    of 2.5.12, pp. 104–105, remain valid with locally null exceptional sets:
    finite Caratheodory tests preserve measurability after these changes.
    Source context: RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualDensity VectorDaniellDualExtension
  MeasureUP RadonMeasureUP RealIntegralFunctionalUP MeasurableFunctionUP PartialFunctionBasic
  SummableRealFunctionUP TotalScalarMeasurability BoundedComponentFamilyUP RadonComponentLocalLinearity
  LocallyNullMeasureUP LocallyNullMeasureModification MeasurableBoundedDualFamily
  MeasurableDualPairing MeasureIntegralUP VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadonDual.
Variable R : realType.
Variable X : topologicalType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Local Notation L := (@compactly_supported_continuous_functions R X).
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hr : is_radon_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L)
  (VectorDaniellHypotheses.variation_integral N Q T).
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_bounded_component_density_family N L T phi kk.
Local Notation k := (vector_density N D kk).
Local Notation kp := (vector_density_point hD kk).

(** Source for [radon_vector_density_component_measurable]:
    locally almost agreement with k_y suffices for measurable
    coordinates in the Radon modification, Federer 2.5.14,
    p. 108; compare the coordinate step in 2.5.12, p. 105. *)
Lemma radon_vector_density_component_measurable (y : E) : D y ->
  is_measure_measurable_function phi (partial_function_total (fun x => (k x y : real_line_metric R))).
Proof.
move=> hy.
have hgood := @radon_component_good_set_locally_almost R X E N hN Q T hQ hM hT
  phi hphi hr hrep D hD.1 kk hkk.
have hm := total_scalar_real_measurable hphi (hkk y).1.1.
apply: (@measurable_total_locally_null_modification R X [the topologicalType of real_line_metric R]
  phi hphi (kk y) (fun x => k x y) (~` density_good_set N D kk) hgood _ hm).
move=> x hx; symmetry; apply: (@vector_density_agree R X E N hN D hD kk x y _ hy).
by apply: contrapT=> hn; exact: hx hn.
Qed.

(** Source for [radon_vector_density_weak_measurable]: weak
    measurability of the selected dual density in Federer
    2.5.14, p. 108, by the countable weak-base proof
    of 2.5.12, p. 105. *)
Theorem radon_vector_density_weak_measurable :
  is_measure_measurable_function phi (partial_function_total kp).
Proof.
apply: (@bounded_dual_family_weak_measurable R X E N hN phi hphi D hD kp).
- exact: vector_density_unit_ball hD kk.
- exact: radon_vector_density_component_measurable.
Qed.

(** Source for [radon_vector_density_norm_measurable]: the
    countable supremum formula for nu* o k in Federer
    2.5.12, p. 105, applied in the Radon modification
    of 2.5.14, p. 108. *)
Theorem radon_vector_density_norm_measurable :
  is_measure_measurable_function phi (real_total_integrand (fun x => dual_norm N (k x))).
Proof.
apply: (@bounded_dual_family_norm_measurable R X E N hN phi hphi D hD kp).
- exact: vector_density_unit_ball hD kk.
- exact: radon_vector_density_component_measurable.
Qed.

(** Source for [radon_vector_density_pairing_summable]: the
    measurable and summable pairing conclusion of 2.5.12,
    p. 103, retained by Federer 2.5.14, p. 108.
    This supporting version takes a total measurable vector map
    and an actual integral of its norm. *)
Theorem radon_vector_density_pairing_summable (eta : X -> E) (b : R) :
  is_measure_measurable_function phi (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_integral phi (real_total_integrand (fun x => N (eta x))) b%:E ->
  exists c : R, is_measure_integral phi (real_total_integrand (fun x => k x (eta x))) c%:E /\ `|c|<=b.
Proof.
move=> heta hi.
have hm := @measurable_unit_dual_pairing R X E N hN D hD phi hphi k
  (fun x => vector_density_unit_ball hD kk x) eta radon_vector_density_component_measurable heta.
apply: (real_total_dominated_integral hphi hm hi)=> x.
exact: vector_density_bound hD kk x (eta x).
Qed.
End RadonDual.
