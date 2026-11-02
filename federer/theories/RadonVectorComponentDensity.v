(** Federer (1969), 2.5.14, p. 108: the scalar component step of 2.5.12, p.
    104, with the Radon measure in place of the lattice-regular measure. The
    Radon representation from 2.5.10, p. 101, removes the unit-series
    hypothesis. The selected scalar density is measurable and pointwise
    bounded; countably measurable support is not required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportFunctionLattice VectorDaniellHypotheses VectorDaniellVariationIntegral
  VectorDaniellDensities MeasureUP RadonMeasureUP RealIntegralFunctionalUP RealLatticeDensityUP
  RadonDominatedCompactDensity TotalScalarLpUP TotalScalarLpClosure TotalScalarArithmetic
  MeasurableTotalBasic SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_vector_component_density]: for each y,
    the function mu_y(f)=T(f y) has a measurable density
    bounded everywhere by nu(y). This is the component step
    of Federer 2.5.12, p. 104, as modified in 2.5.14,
    p. 108. No countable support or global uniqueness is claimed. *)
Theorem radon_vector_component_density (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (VectorDaniellHypotheses.variation_integral N Q T)) (y : E) :
  exists k : X -> R,
    is_real_lattice_density phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (component_integral T y) k /\ forall x, `|k x|<=N y.
Proof.
pose L := @compactly_supported_continuous_functions R X.
have hL := @compactly_supported_continuous_functions_lattice R X.
pose lam := VectorDaniellHypotheses.variation_integral N Q T.
have [->|hy] := eqVneq y 0.
- have hz := @total_scalar_lp_zero R X phi hphi +oo (leey _).
  exists (fun _ => 0); split.
  + split; first exact: hz.2.1.
    move=> f hf; rewrite (@component_integral_zero R X E N L Q T hQ hT f).
    have he : (fun x => f x*0)=(fun _ : X => (0 : R)) by apply: funext=> x; rewrite mulr0.
    rewrite he; exact: real_total_zero_integral hphi.
  + by move=> x; rewrite normr0 (real_seminorm_zero hN.1).
have hNy : 0<N y by rewrite (real_norm_positive hN.1 hN.2).
pose y' := (N y)^-1 *: y.
have hNy' : N y'= 1.
  by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have hb f : positive_function_lattice L f -> `|component_integral T y' f|<=lam (fun x => `|f x|).
  move=> hf; have he : (fun x => `|f x|)=f by apply: funext=> x; rewrite ger0_norm //; exact: hf.2.
  rewrite he; have h := @component_integral_bound R X E N hN L Q T hL hQ hM hT y' f hf.
  by rewrite hNy' mul1r in h.
have [k [hk hkb]] := @radon_dominated_compact_density R X phi hphi hr lam (component_integral T y')
  (@variation_integral_monotone_daniell R X E N hN L Q T hL hQ hM hT) hrep
  (@component_integral_daniell R X E N hN L Q T hL hQ hM hT y') hb.
exists (fun x => N y*k x); split.
- split.
  + apply: (measurable_total_scalar_product hphi); last exact: hk.1.
    exact (@measurable_total_constant R X
      [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
      phi hphi (N y)).
  + move=> f hf; have hi := @real_total_integral_scale R X phi hphi _ (component_integral T y' f) (N y) (hk.2 f hf).
    have he : (fun x => f x*(N y*k x))=(fun x => N y*(f x*k x)).
      by apply: funext=> x; rewrite mulrCA.
    rewrite he.
    have hv : component_integral T y f=N y*component_integral T y' f.
      rewrite /component_integral -(vector_variation_homogeneous hT (N y) (vector_lattice_module_product hM y' hf.1)).
      by congr T; apply: funext=> x; rewrite /y' !scalerA mulrAC mulfV ?gt_eqF // mul1r.
    by rewrite hv.
- move=> x; rewrite normrM (ger0_norm (ltW hNy)).
  have h := ler_wpM2l (ltW hNy) (hkb x); by rewrite mulr1 in h.
Qed.
