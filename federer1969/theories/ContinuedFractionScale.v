(** Federer (1969), 2.2.9, p. 65, supporting comparison of the
    continued-fraction contraction scale with the diameter bounds used by
    the open embedding tree. Four digits per level give a strict bound at
    every positive level. Source context and the grouping convention:
    ContinuedFractionBlocks.v; the tree scale is shared with Federer 2.2.8,
    p. 64. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ClosedCoverTreeUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_tree_scale]: supporting
    strict diameter comparison for Federer 2.2.9, p. 65:
    sixteen to the negative k is smaller than two to the
    negative (k+2) for every positive integer k. *)
Lemma continued_fraction_tree_scale (R : realType) k :
  (0 < k)%N -> ((16 : R)^+k)^-1 < @closed_cover_tree_scale R k.
Proof.
case: k=> [|k]; first by rewrite ltn0.
move=> _; rewrite /closed_cover_tree_scale exprVn.
have h2 : (0 : R) < 2 by rewrite ltr0n.
have h16 : (0 : R) < 16 by rewrite ltr0n.
rewrite (@ltf_pV2 R _ _ (exprn_gt0 _ h16) (exprn_gt0 _ h2)).
elim: k=> [|k IH].
- by rewrite /= -!natrX ltr_nat.
- have hle : (2 : R) <= 16 by rewrite ler_nat.
  have hp : 0 < (16 : R)^+k.+1 by rewrite exprn_gt0.
  have hm : (2 : R) * 2^+(k.+1+2) < 2 * 16^+k.+1.
    by rewrite (ltr_pM2l h2).
  have hh := lt_le_trans hm (ler_wpM2r (ltW hp) hle).
  by rewrite !addSn !exprS in hh *.
Qed.

(** Source for [continued_fraction_scale_small]: supporting
    convergence of the cylinder diameters to zero for the
    continued-fraction limit in Federer 2.2.9, p. 65.
    The elementary Archimedean reciprocal bound suffices. *)
Lemma continued_fraction_scale_small (R : realType) (e : R) :
  0 < e -> exists k : nat, (0 < k)%N /\ ((16 : R)^+k)^-1 < e.
Proof.
move=> he.
have [N hN] := @positive_reciprocal_nat_small R e he.
exists N.+1; split; first exact: ltn0Sn.
have hpow : (0 : R) < 16^+N.+1 by rewrite exprn_gt0 // ltr0n.
have hnat : (0 : R) < N.+1%:R by rewrite ltr0n.
apply: le_lt_trans _ hN.
rewrite (@lef_pV2 R _ _ hpow hnat) -natrX ler_nat.
apply: leq_trans (leqnSn N.+1) _.
exact: ltn_expl (isT : (1 < 16)%N).
Qed.
