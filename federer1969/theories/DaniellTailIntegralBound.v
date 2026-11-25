(** Federer (1969), proof of 2.5.2, p. 93, penultimate sentence: lambda(f)
    bounds the integral of f-f_epsilon after the first increasing limit. We
    bound each finite upper functional term by lambda(f) before passing
    through the integral limit. This is the printed monotone argument with
    the fixed upper bound made explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLayers
  MonotoneDaniellIntegralUP DaniellCoverUP DaniellTruncationGrid DaniellFiniteLayerBounds
  DaniellLayerLimits DaniellPositiveIncreasingIntegral SummableRealFunctionUP
  MeasureIntegralBounds ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_tail_integral_upper_bound]: the inequality
    integral(f-f_epsilon) <= lambda(f) in Federer 2.5.2, p. 93 *)
Theorem daniell_tail_integral_upper_bound (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) e :
  positive_function_lattice L f -> (0 < e)%R ->
  measure_lower_integral mu (real_total_integrand (real_lattice_tail f e)) <= (A f)%:E.
Proof.
move=> hf he.
have h1 : real_step_ceiling e 1=e by rewrite /real_step_ceiling mul1r.
pose u n := real_lattice_layer f e (real_step_ceiling e n.+1).
have hu n : positive_function_lattice L (u n).
  apply: (@real_lattice_layer_member R X L hL f e (real_step_ceiling e n.+1) hf.1 (ltW he)).
  have hle := @real_step_ceiling_monotone R e 1 n.+1 he (leq0n n).
  by rewrite h1 in hle.
have hv := real_lattice_tail_member hL hf.1 (ltW he).
have hinc : real_functions_increase_to u (real_lattice_tail f e).
  have hi := @real_step_layers_increase R X f e e 1 he.
  have heq : (fun n => real_lattice_layer f e (((n+1)%:R)*e)%R)=u.
    by apply: funext=> n; rewrite /u /real_step_ceiling addn1.
  by rewrite heq in hi.
have hilim := daniell_positive_increasing_integral_values hL hA hm hu hv hinc.
apply: (extended_order_limit_upper_bound hilim.2)=> n.
have hn := (daniell_finite_layer_integral_bounds hL hA hm hf he n).2.
rewrite h1 in hn; apply: le_trans hn _.
rewrite real_step_ceiling_zero.
have hcap : (0 <= real_step_ceiling e n)%R := real_step_ceiling_nonnegative n (ltW he).
have hmem := (real_lattice_layer_member hL hf.1 (lexx 0%R) hcap).1.
rewrite lee_fin; apply: (@monotone_daniell_integral_monotone R X L A hA _ f hmem hf.1).
move=> x; rewrite /real_lattice_layer (min_r (hf.2 x)) subr0 ge_min lexx.
by [].
Qed.
