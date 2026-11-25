(** Federer (1969), 2.2.9, p. 65, supporting uniqueness of positive digits
    for the classical continued fraction. For an interior tail, the
    reciprocal of the branch value lies strictly between consecutive
    positive integers. Bell2016, section 1, p. 1, recovers the digit by the
    integer part of that reciprocal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBranches ContinuedFractionBlocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_digit_separation]: supporting
    disjointness of distinct digit cylinders in Federer 2.2.9,
    p. 65. A larger digit places the reciprocal
    denominator beyond every denominator with the smaller digit
    and a tail strictly between zero and one. *)
Lemma continued_fraction_digit_separation (R : realType) a b (s t : R) :
  (a < b)%N -> 0 <= s -> s < 1 -> 0 <= t ->
  continued_fraction_branch b t < continued_fraction_branch a s.
Proof.
move=> hab hs hs1 ht.
have ha := @continued_fraction_denominator_positive R a s hs.
have hb := @continued_fraction_denominator_positive R b t ht.
rewrite /continued_fraction_branch (@ltf_pV2 R _ _ hb ha).
have h1 : a.+1%:R + s < a.+2%:R by rewrite -[a.+2%:R]natr1 ltrD2l.
have h2 : (a.+2%:R : R) <= b.+1%:R by rewrite ler_nat ltnS.
have h3 : b.+1%:R <= b.+1%:R + t by rewrite lerDl.
exact: lt_le_trans h1 (le_trans h2 h3).
Qed.

(** Source for [continued_fraction_digit_unique]: supporting
    uniqueness of the first digit and remaining interior tail
    for the classical map in Federer 2.2.9, p. 65.
    Endpoint tails are excluded because rational endpoints have
    the familiar two finite representations. *)
Lemma continued_fraction_digit_unique (R : realType) a b (s t : R) :
  0 <= s -> s < 1 -> 0 <= t -> t < 1 ->
  continued_fraction_branch a s = continued_fraction_branch b t -> a = b /\ s = t.
Proof.
move=> hs hs1 ht ht1 he.
have hab : a = b.
  case: (ltngtP a b)=> hab //.
  - have hh := @continued_fraction_digit_separation R a b s t hab hs hs1 ht.
    by move: hh; rewrite he ltxx.
  - have hh := @continued_fraction_digit_separation R b a t s hab ht ht1 hs.
    by move: hh; rewrite he ltxx.
subst b; split=> //.
have hh := congr1 (fun x : R => x^-1) he.
rewrite !continued_fraction_branch_reciprocal in hh.
exact (addrI a.+1%:R hh).
Qed.

(** Source for [continued_fraction_block_unique]: supporting
    disjointness of four-digit cylinders for Federer 2.2.9,
    p. 65. Equality with two interior tails forces
    equality of all four digits and of the tails themselves. *)
Lemma continued_fraction_block_unique (R : realType) d e (s t : R) :
  0 < s -> s < 1 -> 0 < t -> t < 1 ->
  continued_fraction_block d s = continued_fraction_block e t -> d = e /\ s = t.
Proof.
move=> hs hs1 ht ht1; case: d=> [[a b] [c d]]; case: e=> [[i j] [k l]].
rewrite /continued_fraction_block /= => he.
have bounds n (x : R) (hx : 0 < x) :
    0 < continued_fraction_branch n x /\ continued_fraction_branch n x < 1.
  split; first exact: (continued_fraction_branch_unit_bounds n (ltW hx)).1.
  exact: continued_fraction_branch_positive_tail hx.
have [hd hd1] := bounds d s hs; have [hc hc1] := bounds c _ hd.
have [hb hb1] := bounds b _ hc.
have [hl hl1] := bounds l t ht; have [hk hk1] := bounds k _ hl.
have [hj hj1] := bounds j _ hk.
have [ha he1] := @continued_fraction_digit_unique R a i _ _ (ltW hb) hb1 (ltW hj) hj1 he.
have [hb' he2] := @continued_fraction_digit_unique R b j _ _ (ltW hc) hc1 (ltW hk) hk1 he1.
have [hc' he3] := @continued_fraction_digit_unique R c k _ _ (ltW hd) hd1 (ltW hl) hl1 he2.
have [hd' hst] := @continued_fraction_digit_unique R d l s t (ltW hs) hs1 (ltW ht) ht1 he3.
by subst i j k l; split.
Qed.
