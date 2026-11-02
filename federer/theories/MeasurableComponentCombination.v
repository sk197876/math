(** Federer (1969), 2.5.12, p. 104: linear combinations of scalar components
    represent the corresponding combinations of vectors. This supporting
    form, needed for 2.5.14, p. 108, assumes measurable densities without
    countable support. Linearity and finite integral arithmetic suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground MeasureUP FunctionLatticeUP
  VectorDaniellHypotheses VectorDaniellDensities VectorDaniellRationalSpan
  RealLatticeDensityUP TotalScalarMeasurability SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_component_density_combination]: the
    linearity calculation on scalar densities in Federer
    2.5.12, p. 104, supporting the Radon extension in
    2.5.14, p. 108. Full L-infinity membership is unnecessary. *)
Lemma measurable_component_density_combination (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hM : is_vector_lattice_module hN L Q)
    (hT : is_vector_variation_functional N L Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (a b : R) (y z : E) (ky kz : X -> R) :
  is_real_lattice_density phi (positive_function_lattice L) (component_integral T y) ky ->
  is_real_lattice_density phi (positive_function_lattice L) (component_integral T z) kz ->
  is_real_lattice_density phi (positive_function_lattice L) (component_integral T (a*:y+b*:z))
    (fun x => a*ky x+b*kz x).
Proof.
move=> hy hz; split.
- have haC : continuous (fun p : R^o * R^o => (a* p.1 : R^o)).
    move=> p; apply: (@continuousM R [the topologicalType of (R^o * R^o)%type]
      (fun _ => a) fst p).
    + exact (@cvg_cst [the topologicalType of R^o] a _ (nbhs p) (nbhs_filter p)).
    + exact: cvg_fst.
  have hbC : continuous (fun p : R^o * R^o => (b* p.2 : R^o)).
    move=> p; apply: (@continuousM R [the topologicalType of (R^o * R^o)%type]
      (fun _ => b) snd p).
    + exact (@cvg_cst [the topologicalType of R^o] b _ (nbhs p) (nbhs_filter p)).
    + exact: cvg_snd.
  have hc : continuous (fun p : R^o * R^o => (a* p.1+b* p.2 : R^o)).
    move=> p; exact (cvgD (haC p) (hbC p)).
  exact: (@total_scalar_continuous_binary_operation R X phi hphi ky kz
    (fun p => a* p.1+b* p.2) hc hy.1 hz.1).
- move=> f hf; rewrite (@component_integral_combination R X E N hN L Q T hQ hM hT a b y z f hf).
  have hi := real_total_integral_add hphi (real_total_integral_scale hphi a (hy.2 f hf))
    (real_total_integral_scale hphi b (hz.2 f hf)).
  have he : (fun x => f x*(a*ky x+b*kz x))=(fun x => a*(f x*ky x)+b*(f x*kz x)).
    by apply: funext=> x; ring.
  by rewrite he.
Qed.
