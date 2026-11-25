(** Federer (1969), 2.5.5, pp. 96–97: algebra of the functional on ordered
    differences and the positive intervals. These are supporting lemmas; no
    monotonicity of the given functional is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_integral_zero]: supporting zero identity in Federer
    2.5.5, pp. 96–97 Membership of some f is retained because the lattice
    definition also permits the empty lattice. *)
Lemma daniell_integral_zero (R : realType) (X : Type) (L : set (X -> R))
    (A : (X -> R) -> R) (hA : is_daniell_integral L A) (f : X -> R) :
  L f -> A (fun _ => 0)=0.
Proof.
move=> hf; have hh := @daniell_integral_scale R X L A hA 0 f (lexx 0) hf.
have he : (fun x => 0 * f x)=(fun _ : X => 0) by apply: funext=> x; rewrite mul0r.
by rewrite he mul0r in hh.
Qed.

(** Source for [daniell_integral_ordered_difference]: additive identity for
    f-k in Federer 2.5.5, p. 96, first proof paragraph *)
Lemma daniell_integral_ordered_difference (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_daniell_integral L A) (f g : X -> R) :
  L f -> L g -> function_le g f -> A (fun x => f x-g x)=A f-A g.
Proof.
move=> hf hg hgf.
have hd := @function_lattice_ordered_difference R X L hL g f hg hf hgf.
have ha := @daniell_integral_add R X L A hA g (fun x => f x-g x) hg hd.
have he : (fun x => g x+(f x-g x))=f by apply: funext=> x; rewrite addrCA subrr addr0.
rewrite he in ha; by rewrite ha addrAC subrr add0r.
Qed.

(** Source for [lattice_positive_order_interval_complement]: k maps to f-k
    within the same interval in Federer 2.5.5, p. 96 f-g is the ordered
    difference used in the following display and in Federer. This is a
    source transcription discrepancy, not an erratum to Federer. *)
Lemma lattice_positive_order_interval_complement (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f k : X -> R) :
  L f -> lattice_positive_order_interval L f k ->
  lattice_positive_order_interval L f (fun x => f x-k x).
Proof.
move=> hf [hk [hk0 hkf]]; split.
- exact: (@function_lattice_ordered_difference R X L hL k f hk hf hkf).
- split=> x; first by rewrite subr_ge0; exact: hkf.
  by rewrite lerBlDr lerDl; exact: hk0.
Qed.

(** Source for [daniell_integral_negative_order_bound]: finiteness of the
    negative variation from that of the positive variation, Federer 2.5.5,
    p. 96, first proof paragraph This supplies an actual upper bound for -mu
    on every admissible interval. *)
Lemma daniell_integral_negative_order_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_daniell_integral L A) (f : X -> R) (b : R) :
  L f -> (forall k, lattice_positive_order_interval L f k -> A k <= b) ->
  forall k, lattice_positive_order_interval L f k -> - A k <= b-A f.
Proof.
move=> hf hb k hk.
have hd := @lattice_positive_order_interval_complement R X L hL f k hf hk.
have hv := hb _ hd.
rewrite (@daniell_integral_ordered_difference R X L A hL hA f k hf hk.1 hk.2.2) in hv.
by rewrite lerBrDr addrC.
Qed.
