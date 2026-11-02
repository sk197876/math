(** Federer (1969), 2.2.9, p. 65: abstract specification of the classical
    map by the limit of the displayed continued fraction. The specification
    uses ordinary consecutive truncations and the real epsilon/N criterion.
    Grouped cylinders are a method of proving existence, not part of the
    public definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import SequenceSpace FiniteContinuedFractions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_continued_fraction_map]: direct limit-map
    specification for the classical homeomorphism mentioned in
    Federer 2.2.9, p. 65. The m-term nested
    fractions converge in ordinary real distance to f(n). *)
Definition is_continued_fraction_map (R : realType)
    (f : positive_sequence_space R -> R) : Prop :=
  forall n (e : R), 0 < e -> exists N : nat, forall m : nat,
    (N <= m)%N -> `|continued_fraction_convergent n m - f n| < e.

(** Source for [continued_fraction_map_unique]: supporting
    uniqueness of the map specified by the printed limit in
    Federer 2.2.9, p. 65. Two candidate values
    would be closer than half their own distance to a common
    sufficiently late convergent. *)
Lemma continued_fraction_map_unique (R : realType)
    (f g : positive_sequence_space R -> R) :
  is_continued_fraction_map f -> is_continued_fraction_map g -> f = g.
Proof.
move=> hf hg; apply: funext=> n; case: (eqVneq (f n) (g n))=> // hne.
have hd : 0 < `|f n - g n| by rewrite normr_gt0 subr_eq0.
pose e := `|f n - g n| / 2.
have he : 0 < e by rewrite /e divr_gt0 // ltr0n.
have [N hN] := hf n e he; have [M hM] := hg n e he.
have h1 := hN (maxn N M) (leq_maxl N M).
have h2 := hM (maxn N M) (leq_maxr N M).
have hh := ler_distD (continued_fraction_convergent n (maxn N M)) (f n) (g n).
rewrite distrC in h1.
have hbad := le_lt_trans hh (ltrD h1 h2).
by move: hbad; rewrite /e -splitr ltxx.
Qed.
