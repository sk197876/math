(** Federer (1969), 2.3.7, pp. 77–78: the thresholds 2^-i tend to zero.
    Source context: UniformPartialConvergenceUP.v. We reuse the identical
    dyadic weights already developed for 2.2.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpaceUP SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [egoroff_threshold]: direct threshold 2^-i in
    Federer 2.3.7, p. 77; our index n corresponds to i=n+1. *)
Definition egoroff_threshold (R : realType) n : R := sequence_metric_weight n.
Arguments egoroff_threshold {R} n.

(** Source for [egoroff_threshold_positive]: supporting positivity
    needed for the vanishing exceptional-set argument in Federer
    2.3.7, p. 78. *)
Lemma egoroff_threshold_positive (R : realType) n : 0 < @egoroff_threshold R n.
Proof. by rewrite /egoroff_threshold /sequence_metric_weight exprn_gt0 // invr_gt0 ltr0n. Qed.

(** Source for [egoroff_threshold_small]: supporting arbitrarily
    small thresholds for the uniform conclusion of Federer 2.3.7,
    p. 78, final display. *)
Lemma egoroff_threshold_small (R : realType) (e : R) : 0 < e ->
  exists n, egoroff_threshold n < e.
Proof.
move=> he; have [n hn] := sequence_inverse_power_small he.
exists n; apply: le_lt_trans _ hn; rewrite /egoroff_threshold /sequence_metric_weight.
apply: ler_wiXn2l; last exact: leqnSn.
- by rewrite invr_ge0 ler0n.
- by rewrite invf_le1 ?ltr0n // ler1n.
Qed.
