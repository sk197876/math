(** Federer (1969), proof of 2.5.2, p. 93: the four inequalities comparing
    three consecutive layers with the measures of the intermediate closed
    upper levels. We retain equal-width arbitrary neighbouring intervals
    before specialising to the epsilon grid. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLayers
  MonotoneDaniellIntegralUP DaniellCoverUP DaniellCoverBasic DaniellCoverMeasure
  DaniellLayerCostBounds DaniellPositiveIntegral RealTotalCharacteristicBounds
  SummableRealFunctionUP MeasureUP MeasureBasic MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_consecutive_layer_integral_bounds]: the
    functional-integral sandwich in Federer 2.5.2, p. 93 The middle integral
    is finite as a consequence of the finite upper functional value, not an
    extra hypothesis. *)
Lemma daniell_consecutive_layer_integral_bounds (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) (a b c d : R) :
  positive_function_lattice L f -> (0 <= a)%R -> (a < b)%R -> (b < c)%R -> (c < d)%R ->
  (b-a=c-b)%R -> (c-b=d-c)%R ->
  (A (real_lattice_layer f c d))%:E <= measure_lower_integral mu (real_total_integrand (real_lattice_layer f b c)) /\
  measure_lower_integral mu (real_total_integrand (real_lattice_layer f b c)) <= (A (real_lattice_layer f a b))%:E.
Proof.
move=> hf ha hab hbc hcd he1 he2.
have hb : (0 <= b)%R := le_trans ha (ltW hab).
have hc : (0 <= c)%R := le_trans hb (ltW hbc).
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
have hlayer := real_lattice_layer_member hL hf.1 hb (ltW hbc).
have hi := (daniell_positive_lattice_integral hL hA hm hlayer).1.
have hB := @daniell_positive_upper_level_measurable R X L A hL hA mu hm f b hf.
have hC := @daniell_positive_upper_level_measurable R X L A hL hA mu hm f c hf.
have hepos : (0 < c-b)%R by rewrite subr_gt0.
split.
- apply: le_trans (daniell_layer_lower_level_cost hL hA hm hf.1 hc hcd) _.
  rewrite -he2.
  have hsub : [set x | (c < f x)%R] `<=` [set x | (c <= f x)%R].
    move=> x hx; exact: ltW hx.
  have hmu := measure_mono hmeasure hsub.
  have he0 : 0 <= (c-b)%R%:E by rewrite lee_fin; exact: ltW hepos.
  apply: le_trans (@lee_wpmul2l R (c-b)%R%:E he0 _ _ hmu) _.
  apply: (@real_total_integral_level_lower_bound R X mu hmeasure [set x | (c <= f x)%R]
    (real_lattice_layer f b c) _ (c-b)%R hC hepos hi hlayer.2)=> x hx.
  by rewrite (real_lattice_layer_full (ltW hbc) hx).
- have hbound : measure_lower_integral mu (real_total_integrand (real_lattice_layer f b c)) <=
      (c-b)%R%:E * mu [set x | (b <= f x)%R].
    apply: (@real_total_integral_supported_upper_bound R X mu hmeasure [set x | (b <= f x)%R]
      (real_lattice_layer f b c) _ (c-b)%R hB hepos hi).
    + move=> x hx; exact: real_lattice_layer_bound (ltW hbc).
    + move=> x hx; apply: real_lattice_layer_zero (ltW hbc) _.
      apply: ltW; rewrite ltNge; apply/negP; exact hx.
  apply: le_trans hbound _; rewrite -he1.
  exact: (@daniell_layer_upper_level_cost R X L A hL hA mu hm f a b hf.1 ha hab).
Qed.
