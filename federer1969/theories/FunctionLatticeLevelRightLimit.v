(** Federer (1969), 2.5.3, p. 94, first display: phi{f>t}=lim_(h down to 0)
    h^-1 lambda(min(f,t+h)-min(f,t)). The proof first obtains the
    reciprocal-sequence limit and then uses monotonicity in every positive
    width to establish the printed arbitrary-width limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp FunctionLatticeLayers
  FunctionLatticeLevelRamps FunctionLatticeLevelIntegral PositiveRightOrderLimit
  RealIntegralFunctionalUP RealIntegralFunctional MonotoneDaniellIntegralUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_lattice_level_ramp_functional]: positive homogeneity
    moves the normalising factor outside lambda in Federer 2.5.3, p. 94,
    first display *)
Lemma real_lattice_level_ramp_functional (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (f : X -> R) (t h : R) :
  L f -> (0 <= t)%R -> (0 < h)%R ->
  A (real_lattice_ramp f t (t+h)%R)=(h^-1 * A (real_lattice_layer f t (t+h)%R))%R.
Proof.
move=> hf ht hh.
have hth : (t <= t+h)%R by rewrite lerDl; exact: ltW hh.
have hmem := (real_lattice_layer_member hL hf ht hth).1.
have hinv : (0 <= h^-1)%R by rewrite invr_ge0; exact: ltW hh.
have he : real_lattice_ramp f t (t+h)%R=
    (fun x => (h^-1 * real_lattice_layer f t (t+h)%R x)%R).
  by apply: funext=> x; rewrite /real_lattice_ramp /real_lattice_layer addrAC subrr add0r.
rewrite he; exact: (@monotone_daniell_integral_scale R X L A hA h^-1%R
  (real_lattice_layer f t (t+h)%R) hinv hmem).
Qed.

(** Source for [represented_lattice_strict_level_right_limit]: direct first
    formula of Federer 2.5.3, p. 94 The limit is taken over all positive
    real h tending to zero, not just a selected sequence. No regularity
    assumption is introduced. *)
Theorem represented_lattice_strict_level_right_limit (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (f : X -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  positive_right_extended_order_limit
    (fun h => (h^-1 * A (real_lattice_layer f t (t+h)%R))%R%:E)
    (mu [set x | (t < f x)%R]).
Proof.
move=> hf ht.
have hD := @real_integral_functional_is_monotone_daniell R X mu hm L A hL hA.
pose u h := (A (real_lattice_ramp f t (t+h)%R))%:E.
have hmem h (hh : (0 < h)%R) : L (real_lattice_ramp f t (t+h)%R).
  have hth : (t < t+h)%R by rewrite ltrDl.
  exact: (real_lattice_ramp_member hL hf.1 (ltW ht) hth).1.
have hmono h k : (0 < h)%R -> (0 < k)%R -> (h <= k)%R -> u k <= u h.
  move=> hh hk hhk; rewrite /u lee_fin.
  apply: (@monotone_daniell_integral_monotone R X L A hD _ _ (hmem k hk) (hmem h hh)).
  exact: (@real_lattice_level_ramp_width_antitone R X f t h k hh hk hhk).
have hseq := @represented_lattice_strict_level_integral_limit R X L A hL mu hm hA f t hf ht.
have hright := @antitone_reciprocal_positive_right_limit R u _ hmono hseq.2.
apply: (@positive_right_extended_order_limit_congr R u _ _ _ hright)=> h hh.
by rewrite /u (@real_lattice_level_ramp_functional R X L A hL hD f t h hf.1 (ltW ht) hh).
Qed.
