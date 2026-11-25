(** Federer (1969), 2.5.5, p. 97, first proof paragraph: split h <= f+g by
    k=min(f,h) and h-k. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellIntegralAlgebra
  DaniellVariationUP DaniellVariationBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lattice_positive_order_interval_add]: supporting inclusion
    of sums of admissible functions in the proof of Federer 2.5.5, p. 97 *)
Lemma lattice_positive_order_interval_add (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f g k l : X -> R) :
  lattice_positive_order_interval L f k -> lattice_positive_order_interval L g l ->
  lattice_positive_order_interval L (fun x => f x+g x) (fun x => k x+l x).
Proof.
move=> [hk [hk0 hkf]] [hl [hl0 hlg]]; split.
- exact: (@function_lattice_add R X L hL k l hk hl).
- split=> x; [exact: addr_ge0 (hk0 x) (hl0 x)|exact: lerD (hkf x) (hlg x)].
Qed.

(** Source for [lattice_positive_order_interval_split]: exact minimum split
    of h in Federer 2.5.5, p. 97 Both pieces lie in L because the difference
    h-min(h,f) is ordered. *)
Lemma lattice_positive_order_interval_split (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f g h : X -> R) :
  positive_function_lattice L f -> positive_function_lattice L g ->
  lattice_positive_order_interval L (fun x => f x+g x) h ->
  lattice_positive_order_interval L f (fun x => Order.min (h x) (f x)) /\
  lattice_positive_order_interval L g (fun x => h x-Order.min (h x) (f x)).
Proof.
move=> hf hg [hh [hh0 hhfg]].
have hk : L (fun x => Order.min (h x) (f x)) := function_lattice_minimum hL hh hf.1.
have hkh : function_le (fun x => Order.min (h x) (f x)) h.
  by move=> x; rewrite ge_min lexx.
split.
- split; first exact: hk.
  split=> x; [by rewrite le_min hh0 hf.2|by rewrite ge_min lexx orbT].
- split; first exact: (@function_lattice_ordered_difference R X L hL _ h hk hh hkh).
  split=> x; first by rewrite subr_ge0; exact: hkh.
  case: (leP (h x) (f x))=> hxf.
  + rewrite subrr; exact: hg.2.
  + by rewrite lerBlDr addrC; exact: hhfg.
Qed.

(** Source for [daniell_positive_variation_add]: additivity of mu+ on L+ in
    Federer 2.5.5, p. 97 The two inequalities follow respectively from the
    minimum split and independent suprema. *)
Theorem daniell_positive_variation_add (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (f g : X -> R) :
  positive_function_lattice L f -> positive_function_lattice L g ->
  P (fun x => f x+g x)= P f+P g.
Proof.
move=> hf hg; pose s x := f x+g x.
have hs : positive_function_lattice L s.
  split; first exact: (@function_lattice_add R X L hL f g hf.1 hg.1).
  move=> x; exact: addr_ge0 (hf.2 x) (hg.2 x).
have hup : P s <= P f+P g.
  apply: (@daniell_positive_variation_least R X L A P hP s _ hs)=> h hh.
  have [hk hd] := @lattice_positive_order_interval_split R X L hL f g h hf hg hh.
  have hb := lerD (@daniell_positive_variation_upper R X L A P hP f _ hf hk)
    (@daniell_positive_variation_upper R X L A P hP g _ hg hd).
  have hkh : function_le (fun x => Order.min (h x) (f x)) h.
    by move=> x; rewrite ge_min lexx.
  rewrite (@daniell_integral_ordered_difference R X L A hL hA h _ hh.1 hk.1 hkh)
    addrCA subrr addr0 in hb.
  exact: hb.
have haux k : lattice_positive_order_interval L f k -> A k+P g <= P s.
  move=> hk.
  have hb : P g <= P s-A k.
    apply: (@daniell_positive_variation_least R X L A P hP g _ hg)=> l hl.
    rewrite lerBrDl -(@daniell_integral_add R X L A hA k l hk.1 hl.1).
    apply: (@daniell_positive_variation_upper R X L A P hP s _ hs).
    exact: (@lattice_positive_order_interval_add R X L hL f g k l hk hl).
  by move: hb; rewrite lerBrDl.
have hlo : P f+P g <= P s.
  have hb : P f <= P s-P g.
    apply: (@daniell_positive_variation_least R X L A P hP f _ hf)=> k hk.
    rewrite lerBrDr; exact: haux k hk.
  by move: hb; rewrite lerBrDr.
apply/eqP; by rewrite eq_le hup hlo.
Qed.
