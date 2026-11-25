(** Federer (1969), 2.5.1, p. 91: maxima, positive and negative parts, and
    the positive sublattice. The May 1987 erratum, p. 2, book p. 91 line 28,
    removes the sign condition from the maximum assertion. We prove the
    corrected unrestricted maximum by f+(g-min(f,g)), using an ordered
    difference. This is a difference from the corrected Federer text. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_lattice_zero]: supporting use of zero in the parts
    assertion of Federer 2.5.1, p. 91 A lattice member is necessary because
    the empty lattice satisfies the definition. *)
Lemma function_lattice_zero (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (f : X -> R) : L f -> L (fun _ => 0).
Proof.
move=> hf; have h := function_lattice_scale hL (lexx 0) hf.
have he : (fun x => 0 * f x)=(fun _ : X => 0) by apply: funext=> x; rewrite mul0r.
by rewrite he in h.
Qed.

(** Source for [function_lattice_maximum]: corrected Federer 2.5.1, p. 91
    line 28; erratum p. 2 removes the sign premise. The ordered difference
    g-min(f,g) gives unrestricted closure without closure under arbitrary
    subtraction. *)
Lemma function_lattice_maximum (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (f g : X -> R) : L f -> L g ->
  L (fun x => Order.max (f x) (g x)).
Proof.
move=> hf hg; have hm := function_lattice_minimum hL hf hg.
have hle : function_le (fun x => Order.min (f x) (g x)) g.
  by move=> x; rewrite ge_min lexx orbT.
have hd := function_lattice_ordered_difference hL hm hg hle.
have ha := function_lattice_add hL hf hd.
have he : (fun x => f x+(g x-Order.min (f x) (g x)))=(fun x => Order.max (f x) (g x)).
  apply: funext=> x; case: (leP (f x) (g x))=> h.
  - by rewrite addrCA subrr addr0.
  - by rewrite subrr addr0.
by rewrite he in ha.
Qed.

(** Source for [function_lattice_positive_part]: positive part closure in
    Federer 2.5.1, p. 91 It follows from maximum closure and the zero
    member. *)
Lemma function_lattice_positive_part (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (f : X -> R) : L f -> L (fun x => Order.max (f x) 0).
Proof. move=> hf; exact: (@function_lattice_maximum R X L hL f (fun _ => 0) hf (function_lattice_zero hL hf)). Qed.

(** Source for [function_lattice_negative_part]: negative part f-minus =
    f-plus minus f in Federer 2.5.1, p. 91 This difference is ordered. *)
Lemma function_lattice_negative_part (R : realType) (X : Type) (L : set (X -> R))
    (hL : is_function_lattice L) (f : X -> R) : L f -> L (fun x => Order.max (-f x) 0).
Proof.
move=> hf; have hp := function_lattice_positive_part hL hf.
have hle : function_le f (fun x => Order.max (f x) 0) by move=> x; rewrite le_max lexx.
have hd := function_lattice_ordered_difference hL hf hp hle.
have he : (fun x => Order.max (f x) 0-f x)=(fun x => Order.max (-f x) 0).
  apply: funext=> x; case: (leP 0 (f x))=> h.
  - by rewrite subrr max_r // oppr_le0.
  - by rewrite sub0r max_l // oppr_ge0 ltW.
by rewrite he in hd.
Qed.

(** Source for [positive_function_lattice_laws]: direct assertion that L+ is
    a lattice in Federer 2.5.1, p. 91 No nonemptiness premise is added, and
    the truncating constant need not be a member. *)
Theorem positive_function_lattice_laws (R : realType) (X : Type) (L : set (X -> R)) :
  is_function_lattice L -> is_function_lattice (positive_function_lattice L).
Proof.
move=> hL; constructor.
- move=> f g [hf hfp] [hg hgp]; split; first exact: (@function_lattice_add R X L hL f g hf hg).
  move=> x; exact: addr_ge0 (hfp x) (hgp x).
- move=> c f hc [hf hfp]; split; first exact: (@function_lattice_scale R X L hL c f hc hf).
  move=> x; exact: mulr_ge0 hc (hfp x).
- move=> f g [hf hfp] [hg hgp]; split; first exact: (@function_lattice_minimum R X L hL f g hf hg).
  by move=> x; rewrite le_min hfp hgp.
- move=> c f hc [hf hfp]; split; first exact: (@function_lattice_truncation R X L hL c f hc hf).
  by move=> x; rewrite le_min hfp hc.
- move=> f g [hf hfp] [hg hgp] hfg; split; first exact: (@function_lattice_ordered_difference R X L hL f g hf hg hfg).
  by move=> x; rewrite subr_ge0; exact: hfg.
Qed.
