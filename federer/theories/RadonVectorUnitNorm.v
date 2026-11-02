(** Federer (1969), 2.5.14, p. 108: the variation supremum argument of
    2.5.12, p. 106, first gives local unit norm for a Radon density. Testing
    against K(X)+ identifies rho=nu* o k with one locally by scalar local
    uniqueness. Global normalization is a separate representative choice;
    locally null is not silently replaced by null. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureAlmostUP MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP FunctionLatticeUP RealIntegralFunctionalUP
  FunctionLatticeRegularityUP CountablyMeasurableUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellWeakMeasurability VectorDaniellPairingMeasurability
  MeasurableDualPairing DualNormEvaluation VectorDaniellVariationIntegral
  SummableRealNormed TotalScalarMeasurability TotalScalarArithmetic
  MeasureStepIntegralIdentification MeasureIntegralComparison RealTotalCharacteristicBounds
  RealLatticeDensityUP RadonLatticeLocalUniqueness MeasurableTotalBasic FunctionLatticeLaws CompactSupportFunctionUP CompactSupportFunctionLattice
  RadonMeasureUP BoundedComponentFamilyUP RadonVectorDensityMeasurability LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section UnitNorm.
Variable R : realType.
Variable X : topologicalType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation L := (@compactly_supported_continuous_functions R X).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
(** Source for [hL]: K(X) lattice laws of Federer 2.5.13, p. 106,
    supporting the vector extension in 2.5.14, p. 108. *)
Let hL := @compactly_supported_continuous_functions_lattice R X.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L)
  (variation_integral N Q T).
Hypothesis hr : is_radon_measure phi.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_bounded_component_density_family N L T phi kk.
Local Notation k := (vector_density N D kk).

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).
Local Notation rho := (fun x => dual_norm N (k x)).

(** Source for [represented_radon_vector_density_locally_unit_norm]: the local version of the unit-norm assertion for
    Federer 2.5.14, p. 108, by the argument of 2.5.12, p. 106. The integral
    representation is an explicit premise here; the theorem
    derives the locally almost-everywhere unit norm. A subsequent
    representative choice supplies the final global normalization. *)
Theorem represented_radon_vector_density_locally_unit_norm :
  (forall w, Q w -> is_measure_integral phi
    (real_total_integrand (fun x => k x (w x))) (T w)%:E) ->
  measure_locally_almost_everywhere phi [set x | rho x = 1].
Proof.
move=> hformula.
have hrho := @radon_vector_density_norm_measurable R X E N hN Q T hQ hM hT phi hphi hr hrep D hD kk hkk.
have hrhos := real_integrand_measurable_scalar_norm hphi hrho.
have hrho0 x : 0 <= rho x.
  exact (@dual_unit_norm_nonnegative R E N hN D hD (k x) (vector_density_unit_ball hD kk x)).
have hrho1 x : rho x <= 1 := (vector_density_unit_ball hD kk x).2.
have hd : is_real_lattice_density phi Lp lam rho.
  split=> // f hf.
  have hfs := real_integrand_measurable_scalar_norm hphi (hrep hf).1.
  have hp := measurable_total_scalar_product hphi hfs hrhos.
  have hpE := measurable_partial_real_embedding hphi (total_scalar_real_measurable hphi hp).
  have hb x : `|f x*rho x| <= f x.
    rewrite normrM (ger0_norm (hf.2 x)) (ger0_norm (hrho0 x)).
    by have := ler_wpM2l (hf.2 x) (hrho1 x); rewrite mulr1.
  have [q [hq hqb]] := real_total_dominated_integral hphi hpE (hrep hf) hb.
  have hqle : q <= lam f := le_trans (ler_norm _) hqb.
  have hlq : lam f <= q.
    apply: (@variation_integral_least R X E N hN L Q T hQ f q hf)=> w hw hwf.
    have hwi := hformula w hw.
    have ho : function_le (fun x => k x (w x)) (fun x => f x*rho x).
      move=> x; apply: le_trans (ler_norm _) _.
      apply: le_trans (dual_norm_evaluation_bound (w x) (vector_density_dual hD kk x)) _.
      rewrite [f x*_]mulrC; exact (ler_wpM2l (hrho0 x) (hwf x)).
    have hh := measure_integral_monotone hphi hwi hq
      (real_total_pointwise_order_almost hphi ho).
    by rewrite lee_fin in hh.
  have hqe : q=lam f by apply/eqP; rewrite eq_le hqle hlq.
  by rewrite -hqe.
have h1 : is_real_lattice_density phi Lp lam (fun _ => 1).
  split.
  - apply: (@real_total_scalar_measurable R X phi hphi (fun _ => 1)).
    exact (@measurable_total_constant R X [the topologicalType of real_line_metric R] phi hphi 1).
  - move=> f hf.
    have he : (fun x => f x*1)=f by apply: funext=> x; rewrite mulr1.
    rewrite he; exact: hrep hf.
exact: (@radon_compact_lattice_density_locally_unique R X phi hphi hr lam lam rho (fun _ => 1) hrep hd h1).
Qed.
End UnitNorm.
