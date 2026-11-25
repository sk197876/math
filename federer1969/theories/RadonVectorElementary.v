(** Federer (1969), 2.5.14, p. 108: the elementary functions f times y are
    represented by the Radon dual density, as in 2.5.12, p. 105. Local
    almost agreement becomes ordinary almost agreement after multiplying by
    f, because its support is compact and has finite measure. Source
    context: RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualDensity VectorDaniellDualExtension
  VectorDaniellElementaryRepresentation BoundedComponentFamilyUP RadonComponentLocalLinearity
  MeasureUP RadonMeasureUP MeasureAlmostUP MeasureAlmostBasic RealIntegralFunctionalUP
  SummableRealFunctionUP MeasureIntegralAlmostEquality LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_vector_density_represents_elementary]:
    the elementary step of G=Q in Federer 2.5.12,
    p. 105, retained in 2.5.14, p. 108, using
    nullity on the compact support of each scalar test. *)
Lemma radon_vector_density_represents_elementary (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_vector_variation_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (VectorDaniellHypotheses.variation_integral N Q T))
    (D : set E) (hD : is_rational_dense_subspace hN D) (kk : E -> X -> R)
    (hkk : is_bounded_component_density_family N (@compactly_supported_continuous_functions R X) T phi kk)
    (f : X -> R) (y : E) :
  positive_function_lattice (@compactly_supported_continuous_functions R X) f -> D y ->
  vector_density_represents N Q T phi D kk (fun x => f x*:y).
Proof.
move=> hf hy; split.
  exact (@vector_lattice_module_product R X E N hN
    (@compactly_supported_continuous_functions R X) Q hM f y hf.1).
have hi := (hkk y).1.2 f hf.
have hgood := @radon_component_good_set_locally_almost R X E N hN Q T hQ hM hT
  phi hphi hr hrep D hD.1 kk hkk.
pose S := real_function_support f.
pose B := S `&` ~` density_good_set N D kk.
have hB : phi B=0%E := hgood S (radon_compact_finite hr hf.1.2).
have ha : measure_almost_everywhere phi (~` B).
  by rewrite /measure_almost_everywhere setCK.
apply: (measure_integral_almost_equal hphi hi).
apply: (measure_almost_everywhere_mono hphi _ ha)=> x hx.
exists (f x*kk y x)%:E; split; first by apply/real_total_integrand_graph.
apply/real_total_integrand_graph.
rewrite (dual_space_scale _ _ (vector_density_dual hD kk x)).
case: (pselect (S x))=> hs.
- have hg : density_good_set N D kk x.
    apply: contrapT=> hn; apply: hx; by split.
  by rewrite (@vector_density_agree R X E N hN D hD kk x y hg hy).
- by rewrite (real_function_zero_off_support hs) !mul0r.
Qed.
