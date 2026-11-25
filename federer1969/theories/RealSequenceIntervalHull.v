(** Supporting interval exhaustion for the arc-length null-preimage argument
    in Federer (1969), 2.9.22, p. 168. The printed interval integral
    estimate is extended to inverse images of sets. These finite prefix
    hulls are order/set-theoretic infrastructure, not an additional claim
    attributed to the book. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_prefix_low]: supporting finite left endpoint
    for the interval-to-set passage in Federer 2.9.22, p. 168;
    it is the minimum of the first n+1 values of a sequence. *)
Fixpoint real_prefix_low (R : realType) (p : nat -> R) (n : nat) : R :=
  if n is k.+1 then Num.min (real_prefix_low p k) (p n) else p 0%N.

(** Source for [real_prefix_high]: supporting finite right endpoint
    for Federer 2.9.22, p. 168; the maximum of the first
    n+1 sequence values, so the resulting hulls are nested. *)
Fixpoint real_prefix_high (R : realType) (p : nat -> R) (n : nat) : R :=
  if n is k.+1 then Num.max (real_prefix_high p k) (p n) else p 0%N.

(** Source for [real_prefix_low_member]: supporting exhaustion for
    Federer 2.9.22, p. 168. Each finite minimum is an actual
    sequence value; no unattained infimum is substituted. *)
Lemma real_prefix_low_member (R : realType) (p : nat -> R) n :
  exists k, (k<=n)%N /\ real_prefix_low p n=p k.
Proof.
elim: n=> [|n [k [hk he]]]; first by exists 0%N.
rewrite /=; case: (leP (real_prefix_low p n) (p n.+1))=> h.
- exists k; split; first exact: leq_trans hk (leqnSn n).
  exact he.
- exists n.+1; split=> //; by rewrite min_r // ltW.
Qed.

(** Source for [real_prefix_high_member]: supporting exhaustion for
    Federer 2.9.22, p. 168. Each finite maximum is an actual
    sequence value, including the initial singleton hull. *)
Lemma real_prefix_high_member (R : realType) (p : nat -> R) n :
  exists k, (k<=n)%N /\ real_prefix_high p n=p k.
Proof.
elim: n=> [|n [k [hk he]]]; first by exists 0%N.
rewrite /=; case: (leP (real_prefix_high p n) (p n.+1))=> h.
- by exists n.+1.
- exists k; split; first exact: leq_trans hk (leqnSn n).
  exact he.
Qed.

(** Source for [real_prefix_low_bound]: supporting coverage by
    finite interval hulls in Federer 2.9.22, p. 168. Every
    value already in the prefix lies above its left endpoint. *)
Lemma real_prefix_low_bound (R : realType) (p : nat -> R) n k :
  (k<=n)%N -> real_prefix_low p n<=p k.
Proof.
elim: n=> [|n ih] in k *.
- by rewrite leqn0=> /eqP->.
- rewrite leq_eqVlt=> /orP [/eqP->|hk].
  + by rewrite /= ge_min lexx orbT.
  + apply: le_trans (_ : Num.min (real_prefix_low p n) (p n.+1)<=real_prefix_low p n) (ih _ hk).
    by rewrite ge_min lexx.
Qed.

(** Source for [real_prefix_high_bound]: supporting coverage by
    finite interval hulls in Federer 2.9.22, p. 168. Every
    value already in the prefix lies below its right endpoint. *)
Lemma real_prefix_high_bound (R : realType) (p : nat -> R) n k :
  (k<=n)%N -> p k<=real_prefix_high p n.
Proof.
elim: n=> [|n ih] in k *.
- by rewrite leqn0=> /eqP->.
- rewrite leq_eqVlt=> /orP [/eqP->|hk].
  + by rewrite /= le_max lexx orbT.
  + apply: le_trans (ih _ hk) (_ : real_prefix_high p n<=Num.max (real_prefix_high p n) (p n.+1)).
    by rewrite le_max lexx.
Qed.

(** Source for [real_prefix_low_antitone]: nested left endpoints
    for the continuity-below argument supporting Federer 2.9.22,
    p. 168; enlarging a finite prefix decreases its minimum. *)
Lemma real_prefix_low_antitone (R : realType) (p : nat -> R) n m :
  (n<=m)%N -> real_prefix_low p m<=real_prefix_low p n.
Proof.
move=> hnm; have [k [hk ->]] := real_prefix_low_member p n.
exact: real_prefix_low_bound (leq_trans hk hnm).
Qed.

(** Source for [real_prefix_high_monotone]: nested right endpoints
    for the continuity-below argument supporting Federer 2.9.22,
    p. 168; enlarging a finite prefix increases its maximum. *)
Lemma real_prefix_high_monotone (R : realType) (p : nat -> R) n m :
  (n<=m)%N -> real_prefix_high p n<=real_prefix_high p m.
Proof.
move=> hnm; have [k [hk ->]] := real_prefix_high_member p n.
exact: real_prefix_high_bound (leq_trans hk hnm).
Qed.
