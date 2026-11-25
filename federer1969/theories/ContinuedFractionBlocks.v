(** Federer (1969), 2.2.9, p. 65, continued-fraction comparison. Grouping
    four positive digits gives uniformly small cylinders whose closed tails
    remain strictly inside the preceding open cylinder. This is a local
    proof device for using the existing abstract embedding-tree laws, not a
    change of the continued fraction or of the sequence-space topology.
    Bell2016, section 2 and Theorem 2, pp. 2 and 5–6, supplies the
    corresponding cylinder background. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBranches ContinuedFractionPairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_block]: supporting grouping
    of four successive terms in the displayed continued fraction
    of Federer 2.2.9, p. 65. Each stored natural
    digit denotes the positive integer one greater than it. *)
Definition continued_fraction_block (R : realType)
    (d : (nat * nat) * (nat * nat)) (t : R) : R :=
  continued_fraction_branch d.1.1 (continued_fraction_branch d.1.2
    (continued_fraction_branch d.2.1 (continued_fraction_branch d.2.2 t))).

(** Source for [continued_fraction_block_inside]: supporting
    strict containment of grouped cylinders for Federer 2.2.9,
    p. 65. Even a zero tail produces an output
    strictly between zero and one after four positive digits. *)
Lemma continued_fraction_block_inside (R : realType) d (t : R) :
  0 <= t -> 0 < continued_fraction_block d t /\ continued_fraction_block d t < 1.
Proof.
move=> ht; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /=.
have hd := (continued_fraction_branch_unit_bounds d ht).1.
have hc := (continued_fraction_branch_unit_bounds c (ltW hd)).1.
have hb := (continued_fraction_branch_unit_bounds b (ltW hc)).1.
split; first exact: (continued_fraction_branch_unit_bounds a (ltW hb)).1.
exact: continued_fraction_branch_positive_tail hb.
Qed.

(** Source for [continued_fraction_block_increasing]: supporting
    preservation of order by four consecutive inverse branches
    in Federer 2.2.9, p. 65; see the even-parity
    cylinder orientation in Bell2016 Theorem 2, p. 5. *)
Lemma continued_fraction_block_increasing (R : realType) d (s t : R) :
  0 <= s -> s < t -> continued_fraction_block d s < continued_fraction_block d t.
Proof.
move=> hs hst; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /=.
have hds := (continued_fraction_branch_unit_bounds d hs).1.
have hcs := (continued_fraction_branch_unit_bounds c (ltW hds)).1.
have hp := @continued_fraction_pair_increasing R c d s t hs hst.
exact: (@continued_fraction_pair_increasing R a b _ _ (ltW hcs) hp).
Qed.

(** Source for [continued_fraction_block_contraction]: supporting
    geometric shrinking for the continued-fraction comparison in
    Federer 2.2.9, p. 65. Four consecutive digits
    contract nonnegative tails by at least a factor sixteen;
    this follows by applying the two-digit estimate twice. *)
Lemma continued_fraction_block_contraction (R : realType) d (s t : R) :
  0 <= s -> 0 <= t ->
  `|continued_fraction_block d t - continued_fraction_block d s| <= `|t-s| / 16.
Proof.
move=> hs ht; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /=.
have hs1 := (continued_fraction_branch_unit_bounds d hs).1.
have ht1 := (continued_fraction_branch_unit_bounds d ht).1.
have hs2 := (continued_fraction_branch_unit_bounds c (ltW hs1)).1.
have ht2 := (continued_fraction_branch_unit_bounds c (ltW ht1)).1.
have hb := @continued_fraction_pair_contraction R a b _ _ (ltW hs2) (ltW ht2).
have hc := @continued_fraction_pair_contraction R c d s t hs ht.
apply: le_trans hb _.
have h4 : (0 : R) <= (4 : R)^-1 by rewrite invr_ge0 ler0n.
have hh := ler_wpM2r h4 hc.
by rewrite -mulrA -invfM -natrM in hh.
Qed.
