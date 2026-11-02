(** Federer (1969), 2.3.9, pp. 79–80: the tails r_j of a finite nonnegative
    series tend to zero. This supporting numerical fact follows from the
    locally developed summation laws of 2.1.1(13), p. 53. Indices start at
    zero; this only shifts the printed positive indexing. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  NonnegativeSumContinuity ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sequence_tail]: the numerical
    tail r_j in Federer 2.3.9, p. 79; it is
    specified using the abstract nonnegative sum of 2.1.1. *)
Definition nonnegative_sequence_tail (R : realType) (a : nat -> \bar R) j :=
  nonnegative_sum [set n | (j <= n)%N] a.

(** Source for [nonnegative_sequence_tail_nonnegative]: supporting
    positivity of the tails in Federer 2.3.9, p. 79. *)
Lemma nonnegative_sequence_tail_nonnegative (R : realType) (a : nat -> \bar R) j :
  0 <= nonnegative_sequence_tail a j.
Proof. exact: nonnegative_sum_nonnegative. Qed.

(** Source for [nonnegative_sequence_tail_antitone]: successive
    tails decrease, supporting Federer 2.3.9, p. 79. *)
Lemma nonnegative_sequence_tail_antitone (R : realType) (a : nat -> \bar R) j k :
  (j <= k)%N -> nonnegative_sequence_tail a k <= nonnegative_sequence_tail a j.
Proof.
move=> hjk; apply: nonnegative_sum_subset=> n hn; exact: leq_trans hjk hn.
Qed.

(** Source for [nonnegative_sequence_tail_finite]: every tail
    of a finite nonnegative sum is finite, as used in Federer
    2.3.9, p. 79, last paragraph. *)
Lemma nonnegative_sequence_tail_finite (R : realType) (a : nat -> \bar R) :
  nonnegative_sum setT a < +oo -> forall j, nonnegative_sequence_tail a j \is a fin_num.
Proof.
move=> hf j; rewrite ge0_fin_numE; last exact: nonnegative_sequence_tail_nonnegative.
apply: le_lt_trans _ hf; apply: nonnegative_sum_subset=> n hn; exact Logic.I.
Qed.

(** Source for [nonnegative_sequence_prefix_tail]: split a
    nonnegative series at j, supporting the tail limit in
    Federer 2.3.9, p. 79. *)
Lemma nonnegative_sequence_prefix_tail (R : realType) (a : nat -> \bar R) j :
  (forall n, 0 <= a n) -> nonnegative_sum setT a =
    nonnegative_sum [set n | (n < j)%N] a + nonnegative_sequence_tail a j.
Proof.
move=> ha; rewrite (@nonnegative_sum_split R nat setT [set n | (n < j)%N] a) // setTI.
congr (_ + _); congr (nonnegative_sum _ a); apply/seteqP; split=> n.
- move=> [_ hn]; change (j <= n)%N; rewrite leqNgt; by apply/negP.
- move=> hn; split=> // hlt; have hn' : (j <= n)%N := hn; by move: hn'; rewrite leqNgt hlt.
Qed.

(** Source for [nonnegative_sequence_tail_small]: tails of a
    finite nonnegative series are eventually smaller than any
    positive real number, supporting Federer 2.3.9, pp. 79–80. *)
Lemma nonnegative_sequence_tail_small (R : realType) (a : nat -> \bar R) :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo ->
  forall e : R, (0 < e)%R -> exists K, forall j, (K <= j)%N -> nonnegative_sequence_tail a j < e%:E.
Proof.
move=> ha hf e he.
pose P j := [set n : nat | (n < j)%N].
have hm n m : (n <= m)%N -> P n `<=` P m.
  move=> hnm k hk; exact: leq_trans hk hnm.
have hs n : P n `<=` setT by move=> k hk.
have hc n : (@setT nat) n -> exists k, P k n by move=> _; exists n.+1; exact: ltnSn.
have hl := @nonnegative_sum_increasing_limit R nat setT P a hm hs hc.
have hfin : nonnegative_sum setT a \is a fin_num.
  by rewrite ge0_fin_numE // nonnegative_sum_nonnegative.
have hlt : nonnegative_sum setT a - e%:E < nonnegative_sum setT a.
  by rewrite -(fineK hfin) -EFinB lte_fin ltrBlDr ltrDl.
have [K hK] := hl.2.1 _ hlt; exists K=> j hj.
have happrox := hK j hj.
rewrite lteBlDr // in happrox.
have hpf : nonnegative_sum (P j) a \is a fin_num.
  rewrite ge0_fin_numE; last exact: nonnegative_sum_nonnegative.
  exact: le_lt_trans (nonnegative_sum_subset a (hs j)) hf.
rewrite (nonnegative_sequence_prefix_tail j ha) in happrox.
by rewrite lteD2lE in happrox.
Qed.
