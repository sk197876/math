(** Federer (1969), 2.5.20, p. 114: the final variation-measure
    identification uses the supremum formula of 2.5.6, p. 98. Bounded
    continuous multipliers approximate arbitrary tests |v|<=f by f*v/(f+e).
    The quotient is continuous even at zeros of f because e>0, and its
    uniform error is at most e. This expands the step Federer says may be
    verified. Source context: CompactFunctionSpaceUP.v The narrow
    normed-type imports provide scalar continuity for addition,
    multiplication, and inversion; the weighted variation argument is proved
    here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactSupportProducts
  CompactUniformNorm ContinuousVectorFamily RegularizedScalarRatio FunctionLatticeUP
  VectorFunctionLattice DaniellIntegralUP DaniellVariationUP DaniellSpaceCompactSpace
  DaniellSpaceCompactness VectorVariationFiniteBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [regularized_continuous_ratio_member]:
    supporting bounded-multiplier approximation for the final
    assertion of Federer 2.5.20, p. 114. Adding e>0
    to the denominator ensures continuity at its zero set. *)
Lemma regularized_continuous_ratio_member (R : realType) (Y : topologicalType)
    (f v : Y -> R) (e : R) :
  compact (@setT Y) -> positive_function_lattice (@compactly_supported_continuous_functions R Y) f ->
  compactly_supported_continuous_functions v -> 0<e ->
  compactly_supported_continuous_functions (fun y => v y/(f y+e)).
Proof.
move=> hY hf hv he.
apply: (@continuous_on_compact_is_compactly_supported R Y (fun y => v y/(f y+e)) hY)=> y.
apply: (@continuousM R Y v (fun z => (f z+e)^-1) y (hv.1 y)).
apply: (@continuousV R Y (fun z => f z+e) y).
- have hpos : 0<f y+e by have := hf.2 y; lra.
  exact: lt0r_neq0 hpos.
- exact (@continuousD R [the normedModType R of R^o] Y f (fun _ => e) y
    (hf.1.1 y) (@cvg_cst [the topologicalType of R^o] e Y (nbhs y) (nbhs_filter y))).
Qed.

(** Source for [compact_daniell_weighted_upper_bound]:
    uniform approximation transfers a bound on f times
    unit-ball multipliers to every v with |v|<=f,
    supporting the last assertion of Federer 2.5.20, p. 114. *)
Lemma compact_daniell_weighted_upper_bound (R : realType) (Y : topologicalType)
    (A : (Y -> R) -> R) (f : Y -> R) (b : R) :
  compact (@setT Y) -> is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  positive_function_lattice (@compactly_supported_continuous_functions R Y) f ->
  (forall r, compactly_supported_continuous_functions r -> (forall y, `|r y|<=1) ->
    A (fun y => f y* r y)<=b) ->
  forall v, compactly_supported_continuous_functions v -> (forall y, `|v y|<=f y) -> A v<=b.
Proof.
move=> hY hA hf hb v hv hvf.
case: (leP (A v) b)=> [h|h]; first by [].
have [C [hC hbound]] := @daniell_sup_norm_bounded R Y hY A hA.
have hden : 0<C+1 by lra.
pose e := (A v-b)/(C+1).
have he : 0<e by rewrite /e divr_gt0 // subr_gt0.
pose r y := v y/(f y+e).
have hr := regularized_continuous_ratio_member hY hf hv he.
have hr1 y : `|r y|<=1 := regularized_scalar_ratio_bound (hf.2 y) (hvf y) he.
have hsmall y : `|f y* r y-v y|<=e := regularized_scalar_ratio_error (hf.2 y) (hvf y) he.
have hprod := compact_support_continuous_multiplier hf.1.1 hr.
have hL := @compact_support_vector_lattice R Y.
have hdiff := vector_function_lattice_difference hL hprod hv.
have hlin := daniell_compact_support_linear hA.
have herr := hbound (fun y => f y* r y-v y) hdiff e (ltW he) hsmall.
rewrite (vector_lattice_additive_difference hL hlin.1 hprod hv) ler_norml in herr.
have [hl hu] := andP herr.
have hbnd := hb r hr hr1.
have hCe : C*e<A v-b.
  have ht : C*e<(C+1)*e by rewrite ltr_pM2r // ltrDl.
  by rewrite [(C+1)*e]mulrC /e divfK ?gt_eqF // in ht.
lra.
Qed.

(** Source for [compact_daniell_weighted_absolute_bound]:
    symmetry of the test class gives the absolute bound
    required by 2.5.6, p. 98, for the verification
    in Federer 2.5.20, p. 114. *)
Lemma compact_daniell_weighted_absolute_bound (R : realType) (Y : topologicalType)
    (A : (Y -> R) -> R) (f : Y -> R) (b : R) :
  compact (@setT Y) -> is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  positive_function_lattice (@compactly_supported_continuous_functions R Y) f ->
  (forall r, compactly_supported_continuous_functions r -> (forall y, `|r y|<=1) ->
    A (fun y => f y* r y)<=b) ->
  forall v, compactly_supported_continuous_functions v -> (forall y, `|v y|<=f y) -> `|A v|<=b.
Proof.
move=> hY hA hf hb v hv hvf.
have hp := compact_daniell_weighted_upper_bound hY hA hf hb hv hvf.
have hnv : forall y, `|-v y|<=f y by move=> y; rewrite normrN; exact: hvf.
have hn := compact_daniell_weighted_upper_bound hY hA hf hb (compactly_supported_opp hv) hnv.
rewrite (daniell_compact_support_opp hA hv) in hn.
rewrite ler_norml; apply/andP; split=> //.
by rewrite lerNl.
Qed.

(** Source for [compact_daniell_weighted_variation_least]:
    the least bound over f times continuous unit-ball
    multipliers equals gamma+(f)+gamma-(f), by 2.5.6,
    p. 98, supporting the final measure identification
    in Federer 2.5.20, p. 114. *)
Theorem compact_daniell_weighted_variation_least (R : realType) (Y : topologicalType)
    (A P Q : (Y -> R) -> R) (f : Y -> R) (b : R) :
  compact (@setT Y) -> is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  positive_function_lattice (@compactly_supported_continuous_functions R Y) f ->
  (forall r, compactly_supported_continuous_functions r -> (forall y, `|r y|<=1) ->
    A (fun y => f y* r y)<=b) -> P f+Q f<=b.
Proof.
move=> hY hA hP hQ hf hb.
have hL := @compact_support_vector_lattice R Y.
have hlin := daniell_compact_support_linear hA.
apply: (@finite_variation_sum_least R Y _ A hL hlin.1 f (P f) (Q f) b
  (hP f hf) (hQ f hf))=> v [hv hvf].
exact (@compact_daniell_weighted_absolute_bound R Y A f b hY hA hf hb v hv hvf).
Qed.
