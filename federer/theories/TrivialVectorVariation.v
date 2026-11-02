(** Federer (1969), 2.5.14, p. 108: zero-dimensional boundary case of the
    vector representation. When E is zero, its variation integral is zero
    and any Radon measure representing it on K(X)+ is the zero measure. This
    supports the almost-everywhere normalization inherited from 2.5.12, p.
    103, without assuming a nonzero vector. Source context:
    RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP VectorDaniellHypotheses VectorDaniellVariationIntegral
  MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity CompactSupportFunctionUP
  CompactCutoffUP CompactCutoff RealIntegralFunctionalUP RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [trivial_vector_variation_zero]: zero-dimensional
    variation boundary case supporting Federer 2.5.14,
    p. 108, from the supremum definition in 2.5.12(5), p. 103. *)
Lemma trivial_vector_variation_zero (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q) (hT : is_vector_variation_functional N L Q T) :
  (forall y : E, y=0) -> forall f, positive_function_lattice L f ->
    VectorDaniellHypotheses.variation_integral N Q T f=0.
Proof.
move=> hE f hf.
have hzero := @variation_zero_map R X E N L Q T hQ hT.
have hn : function_le (fun _ : X => N (0 : E)) f.
  by move=> x; rewrite (real_seminorm_zero hN.1); exact: hf.2.
have hlow := @variation_integral_upper R X E N hN L Q T hQ hT f (fun _ => 0)
  hf (vector_function_space_zero hQ) hn.
rewrite hzero in hlow; apply/eqP; rewrite eq_le hlow andbT.
apply: (@variation_integral_least R X E N hN L Q T hQ f 0 hf)=> w hw _.
have he : w=(fun _ => 0) by apply: funext=> x; exact: hE.
by rewrite he hzero.
Qed.

(** Source for [radon_positive_compact_zero_measure]: the
    zero-functional boundary of the Radon representation in
    Federer 2.5.14, pp. 107–108. Compact cutoffs and
    inner regularity on open sets force all measure values to zero. *)
Lemma radon_positive_compact_zero_measure (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (F : (X -> R) -> R) :
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f -> F f=0) ->
  forall A, mu A=0%E.
Proof.
move=> hrep hzero.
have hKzero K : compact K -> (mu K<=0)%E.
  move=> hK.
  pose u := @compact_cutoff R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
  have hu := @compact_cutoff_specification R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
  have hu0 : function_nonnegative u by move=> x; exact: (andP (compact_cutoff_range hu x)).1.
  have hup : positive_function_lattice (@compactly_supported_continuous_functions R X) u.
    by split=> //; exact: compact_cutoff_function hu.
  have hi := hrep u hup; rewrite (hzero u hup) in hi.
  have h := @real_total_integral_level_lower_bound R X mu hm K u 0%E 1
    (radon_compact_measurable hm hr hK) (@ltr01 R) hi hu0.
  rewrite mul1e in h; apply: h=> x hx.
  have hux : u x = 1 := compact_cutoff_on_set hu hx.
  by rewrite hux.
have hwhole : (mu setT<=0)%E.
  apply: (@radon_inner_least R X mu hr setT openT 0%E)=> K hK _; exact: hKzero.
move=> A; apply/eqP; rewrite eq_le (@measure_nonnegative R X mu hm A) andbT.
apply: le_trans _ hwhole; apply: (@measure_mono R X mu hm)=> x _; exact I.
Qed.
