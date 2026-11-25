(** Federer (1969), 2.5.1–2.5.2, pp. 91–92: positivity and ordering of an
    additive lattice functional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monotone_daniell_integral_zero]: the opening observation in
    the proof of Federer 2.5.2, p. 92 Zero is proved only for a nonempty
    lattice, represented here by a supplied member. *)
Lemma monotone_daniell_integral_zero (R : realType) (X : Type) (L : set (X -> R))
    (A : (X -> R) -> R) (hA : is_monotone_daniell_integral L A) (f : X -> R) :
  L f -> A (fun _ => 0)=0.
Proof.
move=> hf; have hh := monotone_daniell_integral_scale hA (lexx 0) hf.
have he : (fun x => 0 * f x)=(fun _ : X => 0) by apply: funext=> x; rewrite mul0r.
by rewrite he mul0r in hh.
Qed.

(** Source for [monotone_daniell_integral_nonnegative]: the first sentence
    of the proof of Federer 2.5.2, p. 92 *)
Lemma monotone_daniell_integral_nonnegative (R : realType) (X : Type) (L : set (X -> R))
    (A : (X -> R) -> R) (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A)
    (f : X -> R) : L f -> function_nonnegative f -> 0 <= A f.
Proof.
move=> hf hp; rewrite -(monotone_daniell_integral_zero hA hf).
exact: (@monotone_daniell_integral_monotone R X L A hA (fun _ => 0) f
  (function_lattice_zero hL hf) hf hp).
Qed.

(** Source for [positive_additive_lattice_functional_monotone]: supporting
    equivalence of the hypotheses in Federer 2.5.2, p. 92. Ordered
    subtraction suffices; L need not be a vector space. *)
Lemma positive_additive_lattice_functional_monotone (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L) :
  (forall f g, L f -> L g -> A (fun x => f x+g x)=A f+A g) ->
  (forall f, L f -> function_nonnegative f -> 0 <= A f) ->
  forall f g, L f -> L g -> function_le f g -> A f <= A g.
Proof.
move=> hAdd hPos f g hf hg hfg.
pose d x := g x-f x.
have hd := function_lattice_ordered_difference hL hf hg hfg.
have hdp : function_nonnegative d by move=> x; rewrite /d subr_ge0; exact: hfg.
have ha := hAdd f d hf hd.
have he : (fun x => f x+d x)=g by apply: funext=> x; rewrite /d addrCA subrr addr0.
rewrite he in ha; rewrite ha lerDl; exact: hPos d hd hdp.
Qed.
