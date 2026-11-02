(** Federer (1969), proof of 2.5.2, p. 93: functional values of layers
    compared with the measure of their upper and lower levels. The endpoints
    here are arbitrary 0 <= a < b before the printed epsilon-grid
    specialisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp FunctionLatticeLayers
  MonotoneDaniellIntegralUP DaniellCoverUP DaniellCoverBasic DaniellSupportedMinorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_lattice_ramp_upper_bound]: the normalised layer is
    bounded by one, supporting the last inequality of Federer 2.5.2, p. 93 *)
Lemma real_lattice_ramp_upper_bound (R : realType) (X : Type) (f : X -> R) a b x :
  (a < b)%R -> (real_lattice_ramp f a b x <= 1)%R.
Proof.
move=> hab.
have hd : (b-a != 0)%R by rewrite gt_eqF // subr_gt0.
have hp : (0 < (b-a)^-1)%R by rewrite invr_gt0 subr_gt0.
change ((b-a)^-1 * real_lattice_layer f a b x <= 1)%R.
rewrite -(mulVf hd) (ler_pM2l hp); exact: real_lattice_layer_bound (ltW hab).
Qed.

(** Source for [daniell_layer_upper_level_cost]: first inequality in the
    layer display of Federer 2.5.2, p. 93 The constant normalised-layer
    sequence suits {f >= b}, and no measurability of that set is needed for
    this cost estimate. *)
Lemma daniell_layer_upper_level_cost (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) a b :
  L f -> (0 <= a)%R -> (a < b)%R ->
  (b-a)%R%:E * mu [set x | (b <= f x)%R] <= (A (real_lattice_layer f a b))%:E.
Proof.
move=> hf ha hab; pose h := real_lattice_ramp f a b.
have hh : positive_function_lattice L h := real_lattice_ramp_member hL hf ha hab.
have hs : is_daniell_suiting_sequence L [set x | (b <= f x)%R] (fun _ : nat => h).
  split; first by move=> n.
  split; first by move=> n m hnm x; exact: lexx.
  move=> x hx r hr; exists 0%N; by rewrite /h (real_lattice_ramp_one hab hx).
have hbnd := daniell_cover_lower hm hs (daniell_constant_sequence_cost A h).
have hd : (b-a != 0)%R by rewrite gt_eqF // subr_gt0.
have hip : (0 <= (b-a)^-1)%R by rewrite invr_ge0 subr_ge0; exact: ltW hab.
have hmem := (real_lattice_layer_member hL hf ha (ltW hab)).1.
have he : A h=((b-a)^-1 * A (real_lattice_layer f a b))%R :=
  @monotone_daniell_integral_scale R X L A hA (b-a)^-1%R (real_lattice_layer f a b) hip hmem.
rewrite he in hbnd.
have hp : 0 < (b-a)%R%:E by rewrite lte_fin subr_gt0.
have hfin : (b-a)%R%:E \is a fin_num by [].
have hc : (b-a)%R%:E * mu [set x | (b <= f x)%R] <=
    (b-a)%R%:E * ((b-a)^-1 * A (real_lattice_layer f a b))%R%:E.
  by rewrite (lee_pmul2l hfin hp).
by rewrite -EFinM mulrA (mulfV hd) mul1r in hc.
Qed.

(** Source for [daniell_layer_lower_level_cost]: last inequality in the
    layer display of Federer 2.5.2, p. 93 The supported-minorant estimate
    gives this bound with the strict support {f > a}; enlarging to {f >= a}
    gives the book's version for the next layer. *)
Lemma daniell_layer_lower_level_cost (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) a b :
  L f -> (0 <= a)%R -> (a < b)%R ->
  (A (real_lattice_layer f a b))%:E <= (b-a)%R%:E * mu [set x | (a < f x)%R].
Proof.
move=> hf ha hab; pose h := real_lattice_ramp f a b.
have hh : positive_function_lattice L h := real_lattice_ramp_member hL hf ha hab.
have hb x : (a < f x)%R -> (h x <= 1)%R.
  move=> hx; exact: real_lattice_ramp_upper_bound hab.
have hz x : ~ (a < f x)%R -> h x=0%R.
  move=> hx; apply: real_lattice_ramp_zero (ltW hab) _.
  rewrite leNgt; apply/negP; exact hx.
have hbnd := daniell_supported_minorant_bound hL hA hm hh hb hz.
have hd : (b-a != 0)%R by rewrite gt_eqF // subr_gt0.
have hip : (0 <= (b-a)^-1)%R by rewrite invr_ge0 subr_ge0; exact: ltW hab.
have hmem := (real_lattice_layer_member hL hf ha (ltW hab)).1.
have he : A h=((b-a)^-1 * A (real_lattice_layer f a b))%R :=
  @monotone_daniell_integral_scale R X L A hA (b-a)^-1%R (real_lattice_layer f a b) hip hmem.
rewrite he in hbnd.
have hp : 0 < (b-a)%R%:E by rewrite lte_fin subr_gt0.
have hfin : (b-a)%R%:E \is a fin_num by [].
have hc : (b-a)%R%:E * ((b-a)^-1 * A (real_lattice_layer f a b))%R%:E <=
    (b-a)%R%:E * mu [set x | (a < f x)%R].
  by rewrite (lee_pmul2l hfin hp).
by rewrite -EFinM mulrA (mulfV hd) mul1r in hc.
Qed.
