(** Federer (1969), 2.2.6, p. 63: arbitrarily small geometric metric tails.
    We reduce the scalar limit to the local Archimedean reciprocal bound.
    Source context: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ExtendedRealReciprocalBounds SequenceSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sequence_inverse_power_small]: Federer
    2.2.6, p. 63, supporting geometric-tail limit: for each
    positive epsilon some 2^-N is smaller than epsilon. The proof
    uses N+1 at most 2^N and the Archimedean reciprocal estimate. *)
Lemma sequence_inverse_power_small (R : realType) (epsilon : R) :
  0 < epsilon -> exists N, (2^-1)^+N < epsilon.
Proof.
move=> he; have [N hN] := positive_reciprocal_nat_small he.
exists N; apply: le_lt_trans _ hN.
have hpow : (0 < (2 : R)^+N)%R by rewrite exprn_gt0 // ltr0n.
have hnat : (0 < N.+1%:R :> R)%R by rewrite ltr0n.
rewrite exprVn lef_pV2 //.
rewrite -natrX ler_nat; exact: ltn_expl (ltnSn 1).
Qed.

(** Source for [sequence_metric_weight_antitone]: Federer
    2.2.6, p. 63, supporting monotonicity of weights: later
    coordinate weights do not exceed earlier ones. *)
Lemma sequence_metric_weight_antitone (R : realType) n m :
  (n <= m)%N -> @sequence_metric_weight R m <= sequence_metric_weight n.
Proof.
move=> hnm; apply: ler_wiXn2l.
- by rewrite invr_ge0 ler0n.
- by rewrite invf_le1 ?ltr0n // ler1n.
- exact hnm.
Qed.
