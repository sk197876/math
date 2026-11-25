(** Federer (1969), 2.2.9, p. 65, classical continued-fraction comparison.
    Supporting identities and uniform contraction for two successive inverse
    branches. Bell2016, Measure theory and Perron-Frobenius operators for
    continued fractions, 18 April 2016, section 2, pp. 2 and 5–6, gives the
    convergent and cylinder formulas; the two-step bound below is a local
    consequence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_pair_formula]: supporting
    two-digit identity for the fraction displayed in Federer
    2.2.9, p. 65: 1/(a+1/(b+t)) equals
    (b+t)/(a*(b+t)+1). Digits here are zero based. *)
Lemma continued_fraction_pair_formula (R : realType) a b (t : R) :
  0 <= t -> continued_fraction_branch a (continued_fraction_branch b t) =
    (b.+1%:R + t) / (a.+1%:R * (b.+1%:R + t) + 1).
Proof.
move=> ht; have hb := @continued_fraction_denominator_positive R b t ht.
have hb0 : b.+1%:R + t != 0 by rewrite gt_eqF.
rewrite /continued_fraction_branch.
have he : a.+1%:R + (b.+1%:R + t)^-1 =
    (a.+1%:R * (b.+1%:R + t) + 1) / (b.+1%:R + t).
  by rewrite mulrDl mulfK // mul1r.
by rewrite he invf_div.
Qed.

(** Source for [continued_fraction_pair_denominator]: supporting
    uniform denominator estimate for the continued-fraction
    cylinders in Federer 2.2.9, p. 65. Positive
    digits and a nonnegative tail make the denominator at least two. *)
Lemma continued_fraction_pair_denominator (R : realType) a b (t : R) :
  0 <= t -> 2 <= a.+1%:R * (b.+1%:R + t) + 1.
Proof.
move=> ht; rewrite -[2]/(1+1) lerD2r.
have ha : (1 : R) <= a.+1%:R by rewrite ler1n.
have hb : (1 : R) <= b.+1%:R + t.
  have hb1 : (1 : R) <= b.+1%:R by rewrite ler1n.
  have hh := lerD hb1 ht.
  by rewrite addr0 in hh.
by have hh := ler_pM (ler01 : (0 : R) <= 1) (ler01 : (0 : R) <= 1) ha hb;
   rewrite mul1r in hh.
Qed.

(** Source for [continued_fraction_pair_difference]: supporting
    exact difference of two two-digit tails for Federer 2.2.9,
    p. 65. It is the elementary determinant-one
    cancellation behind the cylinder length in Bell2016, p. 6. *)
Lemma continued_fraction_pair_difference (R : realType) a b (s t : R) :
  0 <= s -> 0 <= t ->
  continued_fraction_branch a (continued_fraction_branch b t) -
  continued_fraction_branch a (continued_fraction_branch b s) =
  (t-s) / ((a.+1%:R * (b.+1%:R + t) + 1) *
           (a.+1%:R * (b.+1%:R + s) + 1)).
Proof.
move=> hs ht.
rewrite !continued_fraction_pair_formula //.
pose A : R := a.+1%:R; pose B : R := b.+1%:R.
have hd u (hu : 0 <= u) : A * (B+u) + 1 != 0.
  have h2 : (0 : R) < 2 by rewrite ltr0n.
  have hp := lt_le_trans h2 (@continued_fraction_pair_denominator R a b u hu).
  by rewrite gt_eqF.
have hds := hd s hs; have hdt := hd t ht.
change ((B+t)/(A*(B+t)+1) - (B+s)/(A*(B+s)+1) =
  (t-s)/((A*(B+t)+1)*(A*(B+s)+1))).
rewrite -mulNr addf_div // mulNr.
congr (_ / _).
rewrite [(B+t)*(_+1)]mulrDr [(B+s)*(_+1)]mulrDr !mulr1.
have hc : (B+t) * (A*(B+s)) = (B+s) * (A*(B+t)).
  by rewrite [LHS]mulrCA [RHS]mulrCA [(B+t)*(B+s)]mulrC.
by rewrite hc opprD addrACA subrr add0r opprD addrACA subrr add0r.
Qed.

(** Source for [continued_fraction_pair_contraction]: supporting
    uniform shrinking of continued-fraction cylinders in Federer
    2.2.9, p. 65. Two positive digits contract
    the nonnegative tail by a factor at most one fourth;
    this elementary bound replaces the general convergent-denominator
    estimate in Bell2016, p. 6. *)
Lemma continued_fraction_pair_contraction (R : realType) a b (s t : R) :
  0 <= s -> 0 <= t ->
  `|continued_fraction_branch a (continued_fraction_branch b t) -
    continued_fraction_branch a (continued_fraction_branch b s)| <= `|t-s| / 4.
Proof.
move=> hs ht; rewrite continued_fraction_pair_difference // normf_div.
pose ds : R := a.+1%:R * (b.+1%:R + s) + 1.
pose dt : R := a.+1%:R * (b.+1%:R + t) + 1.
have h2 : (0 : R) < 2 by rewrite ltr0n.
have hs2 : 2 <= ds := @continued_fraction_pair_denominator R a b s hs.
have ht2 : 2 <= dt := @continued_fraction_pair_denominator R a b t ht.
have hprod : (4 : R) <= dt * ds.
  have hh := ler_pM (ltW h2) (ltW h2) ht2 hs2.
  by rewrite -natrM in hh.
have h4 : (0 : R) < 4 by rewrite ltr0n.
have hp : 0 < dt * ds := lt_le_trans h4 hprod.
rewrite [`|_ * _|]ger0_norm; last exact: ltW hp.
apply: ler_wpM2l; first exact: normr_ge0.
by rewrite (@lef_pV2 R _ _ hp h4).
Qed.

(** Source for [continued_fraction_pair_increasing]: supporting
    orientation of even continued-fraction cylinders in Federer
    2.2.9, p. 65, matching Bell2016 Theorem 2,
    p. 5. Two inverse branches preserve strict order. *)
Lemma continued_fraction_pair_increasing (R : realType) a b (s t : R) :
  0 <= s -> s < t ->
  continued_fraction_branch a (continued_fraction_branch b s) <
  continued_fraction_branch a (continued_fraction_branch b t).
Proof.
move=> hs hst.
have hb := @continued_fraction_branch_decreasing R b s t hs hst.
have ht0 := ltW (continued_fraction_branch_unit_bounds b (le_trans hs (ltW hst))).1.
exact: (@continued_fraction_branch_decreasing R a _ _ ht0 hb).
Qed.
