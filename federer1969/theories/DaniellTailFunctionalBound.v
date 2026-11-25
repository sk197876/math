(** Federer (1969), proof of 2.5.2, p. 93, penultimate sentence:
    lambda(f-f_(2epsilon)) is bounded by integral(f). We apply increasing
    continuity of lambda to the finite lower functional terms, bounding the
    middle integrals by integral(f). The final lemma reparametrises 2
    epsilon as an arbitrary positive cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLayers MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellTruncationGrid DaniellFiniteLayerBounds DaniellLayerLimits
  DaniellLayerOrder DaniellPositiveIntegral RealTotalCharacteristicBounds SummableRealFunctionUP
  MeasureIntegralBounds MeasureIntegralComparison ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_double_tail_functional_bound]: the lower inequality
    after the first increasing limit in Federer 2.5.2, p. 93 *)
Lemma daniell_double_tail_functional_bound (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) e :
  positive_function_lattice L f -> (0 < e)%R ->
  (A (real_lattice_tail f (real_step_ceiling e 2)))%:E <= measure_lower_integral mu (real_total_integrand f).
Proof.
move=> hf he.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
have hp n : (0 <= real_step_ceiling e n)%R := real_step_ceiling_nonnegative n (ltW he).
pose u n := real_lattice_layer f (real_step_ceiling e 2) (real_step_ceiling e n.+1.+1).
have hu n : positive_function_lattice L (u n).
  apply: (@real_lattice_layer_member R X L hL f (real_step_ceiling e 2)
    (real_step_ceiling e n.+1.+1) hf.1 (hp 2%N)).
  apply: (@real_step_ceiling_monotone R e 2 n.+1.+1 he); exact: leq0n.
have hv := real_lattice_tail_member hL hf.1 (hp 2%N).
have hinc : real_functions_increase_to u (real_lattice_tail f (real_step_ceiling e 2)).
  have hi := @real_step_layers_increase R X f (real_step_ceiling e 2) e 2 he.
  have heq : (fun n => real_lattice_layer f (real_step_ceiling e 2)
      (((n+2)%:R)*e)%R)=u.
    by apply: funext=> n; rewrite /u /real_step_ceiling addn2.
  by rewrite heq in hi.
have hlim := @monotone_daniell_integral_increases R X L A hA u _ (fun n => (hu n).1) hv.1 hinc.
apply: (extended_order_limit_upper_bound hlim.2)=> n.
have hn := (daniell_finite_layer_integral_bounds hL hA hm hf he n).1.
apply: le_trans hn _.
have hordered : (real_step_ceiling e 1 <= real_step_ceiling e n.+1)%R.
  apply: (@real_step_ceiling_monotone R e 1 n.+1 he); exact: leq0n.
have hmemb := real_lattice_layer_member hL hf.1 (hp 1%N) hordered.
have hib := (daniell_positive_lattice_integral hL hA hm hmemb).1.
have hif := (daniell_positive_lattice_integral hL hA hm hf).1.
apply: (@measure_integral_monotone R X mu hmeasure _ _ _ _ hib hif).
apply: (@real_total_pointwise_order_almost R X mu hmeasure
  (real_lattice_layer f (real_step_ceiling e 1) (real_step_ceiling e n.+1)) f).
exact: (@real_lattice_layer_below_function R X f (real_step_ceiling e 1)
  (real_step_ceiling e n.+1) hf.2 (hp 1%N)).
Qed.

(** Source for [daniell_tail_functional_lower_bound]: the lower tail bound
    of Federer 2.5.2, p. 93 *)
Lemma daniell_tail_functional_lower_bound (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) c :
  positive_function_lattice L f -> (0 < c)%R ->
  (A (real_lattice_tail f c))%:E <= measure_lower_integral mu (real_total_integrand f).
Proof.
move=> hf hc.
have hhalf : (0 < c/2)%R by rewrite divr_gt0 // ltr0n.
have hh := daniell_double_tail_functional_bound hL hA hm hf hhalf.
have h2 : (2%R : R) != 0%R by rewrite pnatr_eq0.
have he : real_step_ceiling (c/2)%R 2=c by rewrite /real_step_ceiling mulrC divfK.
by rewrite he in hh.
Qed.
