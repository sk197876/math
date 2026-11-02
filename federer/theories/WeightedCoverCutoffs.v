(** Federer (1969), 2.10.24, p. 187: supporting positive cutoffs for
    increasingly fine weighted cover choices. All cutoffs stay below a
    prescribed positive extended cutoff and tend uniformly to zero along the
    natural indices. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import CaratheodoryBorelRegular ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_cofinal_metric_cutoffs]: supporting
    cutoff sequence for the countable cover assembly
    in 2.10.24, p. 187. The prescribed
    outer cutoff may be infinity. *)
Lemma positive_cofinal_metric_cutoffs (R : realType) (delta : \bar R) :
  0<delta -> exists r : nat -> R,
    (forall n, (0<r n)%R /\ (r n)%:E<=delta) /\
    (forall e : R, (0<e)%R -> exists N, forall n, (N<=n)%N -> (r n<=e)%R).
Proof.
move=> hd; have [k hk] := reciprocal_metric_cutoffs_cofinal hd.
pose r n := Order.min ((k.+1%:R : R)^-1)%R ((n.+1%:R : R)^-1)%R.
exists r; split.
- move=> n; split.
  + by rewrite /r lt_min !invr_gt0 !ltr0n.
  + apply: le_trans _ hk; by rewrite lee_fin /r ge_min lexx.
- move=> e he.
  have heE : 0<e%:E by rewrite lte_fin.
  have [N hN] := (@reciprocal_natural_order_limit R).2 e%:E heE.
  exists N=> n hn.
  have hrec := hN n hn; rewrite lte_fin in hrec.
  apply: le_trans _ (ltW hrec); by rewrite /r ge_min lexx orbT.
Qed.
