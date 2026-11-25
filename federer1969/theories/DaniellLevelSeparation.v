(** Federer (1969), proof of 2.5.2, p. 93: the separation inequality for
    lower and upper levels of a positive lattice function. We first prove
    the inequality directly for sets, before adapting it to the project's
    partial-function criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRamp
  MonotoneDaniellIntegralUP DaniellCoverUP DaniellCoverBasic DaniellCoverMeasure
  DaniellSequenceSplitting MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cutoff_separation]: the inequality phi(A)+phi(B) <=
    phi(T) obtained from k_n and g_n-k_n in Federer 2.5.2, p. 93 Here A and
    B are the cutoff's zero and one sets inside T, a supporting formulation
    of that argument. *)
Lemma daniell_cutoff_separation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (T : set X) (h : X -> R) :
  positive_function_lattice L h ->
  mu (T `&` [set x | h x=0%R])+mu (T `&` [set x | h x= 1%R]) <= mu T.
Proof.
move=> hh; apply: (daniell_cover_greatest hm)=> g c hg hc.
pose k n x := Order.min (g n x) (h x).
pose r n x := (g n x-k n x)%R.
have hk : is_daniell_suiting_sequence L (T `&` [set x | h x= 1%R]) k :=
  daniell_suiting_cutoff hL hg hh.
have hr : is_daniell_suiting_sequence L (T `&` [set x | h x=0%R]) r :=
  daniell_suiting_remainder hL hg hh.
have [d hd] := daniell_sequence_cost_exists A k.
have [e he] := daniell_sequence_cost_exists A r.
apply: le_trans (leeD (daniell_cover_lower hm hr he) (daniell_cover_lower hm hk hd)) _.
rewrite addeC; apply: (@daniell_split_cost_bound R X L A hL hA T _ _ g k r c d e hg hk hr hc hd he)=> n x.
by rewrite /r addrCA subrr addr0.
Qed.

(** Source for [daniell_positive_level_separation]: the first displayed
    inequality of Federer 2.5.2, p. 93 The negative lower threshold is
    handled separately, exactly as in the printed proof. *)
Theorem daniell_positive_level_separation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) :
  positive_function_lattice L f -> forall (T : set X) (a b : R), (a < b)%R ->
  mu (T `&` [set x | (f x <= a)%R])+mu (T `&` [set x | (b <= f x)%R]) <= mu T.
Proof.
move=> hf T a b hab.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
case: (boolP (0 <= a)%R)=> ha.
- pose h := real_lattice_ramp f a b.
  have hh : positive_function_lattice L h := real_lattice_ramp_member hL hf.1 ha hab.
  have hlow : (T `&` [set x | (f x <= a)%R]) `<=` (T `&` [set x | h x=0%R]).
    move=> x [hx hxa]; split=> //; exact: real_lattice_ramp_zero (ltW hab) hxa.
  have hupp : (T `&` [set x | (b <= f x)%R]) `<=` (T `&` [set x | h x= 1%R]).
    move=> x [hx hbx]; split=> //; exact: real_lattice_ramp_one hab hbx.
  apply: le_trans (leeD (measure_mono hmeasure hlow) (measure_mono hmeasure hupp)) _.
  exact: (@daniell_cutoff_separation R X L A hL hA mu hm T h hh).
- have hnil : (T `&` [set x | (f x <= a)%R])=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [_ hxa]; exfalso; move: ha.
    by rewrite (le_trans (hf.2 x) hxa).
  rewrite hnil (measure_empty hmeasure) add0e.
  apply: (@measure_mono R X mu hmeasure (T `&` [set x | (b <= f x)%R]) T)=> x [hx _]; exact hx.
Qed.
