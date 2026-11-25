(** Federer (1969), 2.2.9, p. 65: finite prefixes of the classical continued
    fraction, grouped into four-digit blocks solely for the shrinking-tree
    proof. Words are stored in reverse order, as in SequenceTreePrefixes.v.
    The digit decoding is a parameter here; no surjectivity or injectivity
    is needed for these finite-expression estimates. Source context and
    supporting cylinder reference: ContinuedFractionBlocks.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBlocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_word]: supporting finite
    expression for Federer 2.2.9, p. 65. Appending
    a block in the stored reversed word inserts it at the
    innermost end of the existing fraction. *)
Fixpoint continued_fraction_word (R : realType)
    (d : nat -> (nat * nat) * (nat * nat)) (s : seq nat) (t : R) : R :=
  if s is j :: r then continued_fraction_word d r (continued_fraction_block (d j) t)
  else t.

(** Source for [continued_fraction_word_unit]: supporting
    preservation of the closed unit interval by finite fractions
    in Federer 2.2.9, p. 65, including the empty
    prefix as the identity. *)
Lemma continued_fraction_word_unit (R : realType) d s (t : R) :
  0 <= t -> t <= 1 ->
  0 <= continued_fraction_word d s t /\ continued_fraction_word d s t <= 1.
Proof.
elim: s t=> [|j s IH] t ht h1 /=; first by split.
have [hl hu] := continued_fraction_block_inside (d j) ht.
exact: IH _ (ltW hl) (ltW hu).
Qed.

(** Source for [continued_fraction_word_positive]: supporting
    nonnegative output of every finite grouped prefix in Federer
    2.2.9, p. 65, for arbitrary nonnegative tails. *)
Lemma continued_fraction_word_positive (R : realType) d s (t : R) :
  0 <= t -> 0 <= continued_fraction_word d s t.
Proof.
elim: s t=> [|j s IH] t ht //=.
exact: IH _ (ltW (continued_fraction_block_inside (d j) ht).1).
Qed.

(** Source for [continued_fraction_word_increasing]: supporting
    order preservation of even-length prefixes of the continued
    fraction in Federer 2.2.9, p. 65; Bell2016
    Theorem 2, p. 5, gives the corresponding cylinder orientation. *)
Lemma continued_fraction_word_increasing (R : realType) d s (u v : R) :
  0 <= u -> u < v ->
  continued_fraction_word d s u < continued_fraction_word d s v.
Proof.
elim: s u v=> [|j s IH] u v hu huv //=.
apply: IH.
- exact: ltW (continued_fraction_block_inside (d j) hu).1.
- exact: continued_fraction_block_increasing hu huv.
Qed.

(** Source for [continued_fraction_word_monotone]: supporting
    nonstrict endpoint comparison for the same finite prefixes in
    Federer 2.2.9, p. 65. *)
Lemma continued_fraction_word_monotone (R : realType) d s (u v : R) :
  0 <= u -> u <= v ->
  continued_fraction_word d s u <= continued_fraction_word d s v.
Proof.
move=> hu; rewrite le_eqVlt=> /orP[/eqP->|huv]; first exact: lexx.
exact: ltW (continued_fraction_word_increasing d s hu huv).
Qed.

(** Source for [continued_fraction_word_contraction]: supporting
    shrinking estimate for the continued-fraction tree in Federer
    2.2.9, p. 65. Each stored block contains four
    digits and contributes a factor one sixteenth. *)
Lemma continued_fraction_word_contraction (R : realType) d s (u v : R) :
  0 <= u -> 0 <= v ->
  `|continued_fraction_word d s v - continued_fraction_word d s u| <=
    `|v-u| / (16 : R) ^+ (size s).
Proof.
elim: s u v=> [|j s IH] u v hu hv /=; first by rewrite expr0 divr1.
have hbu := ltW (continued_fraction_block_inside (d j) hu).1.
have hbv := ltW (continued_fraction_block_inside (d j) hv).1.
have hh := IH _ _ hbu hbv.
apply: le_trans hh _.
have hn : (0 : R) <= ((16 : R) ^+ size s)^-1.
  by rewrite invr_ge0 exprn_ge0 // ler0n.
have hb := @continued_fraction_block_contraction R (d j) u v hu hv.
have hm := ler_wpM2r hn hb.
by rewrite -mulrA -invfM -exprS in hm.
Qed.

(** Source for [continued_fraction_word_injective]: supporting
    uniqueness of an interior tail for a fixed finite prefix
    in Federer 2.2.9, p. 65, derived from the
    even-prefix order preservation rather than from a construction. *)
Lemma continued_fraction_word_injective (R : realType) d s (u v : R) :
  0 <= u -> 0 <= v ->
  continued_fraction_word d s u = continued_fraction_word d s v -> u = v.
Proof.
move=> hu hv he; case: (ltgtP u v)=> huv //.
- have hh := continued_fraction_word_increasing d s hu huv.
  by move: hh; rewrite he ltxx.
- have hh := continued_fraction_word_increasing d s hv huv.
  by move: hh; rewrite he ltxx.
Qed.
