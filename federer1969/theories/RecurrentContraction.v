(** Federer (1969), proof of 2.8.2, pp. 142–143: the error is multiplied by
    sigma(A)^(1/2) infinitely often, so its nonincreasing finite sequence
    tends to zero. The real arithmetic below uses the existing Archimedean
    geometric-power bound, without importing a theorem about measures or
    convergence of integral sequences. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GeometricPowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [covering_contraction_root_bounds]: the strict slack sigma <
    sqrt(sigma) < 1 used to select a finite subfamily in Federer 2.8.2, p.
    142, final display The square root is exactly the one chosen in the
    printed proof. *)
Lemma covering_contraction_root_bounds (R : realType) (sigma : R) :
  0 < sigma < 1 ->
  (0 < Num.sqrt sigma < 1) /\ sigma < Num.sqrt sigma.
Proof.
move=> /andP [hs0 hs1].
have hq0 : 0 < Num.sqrt sigma by rewrite sqrtr_gt0.
have hq1 : Num.sqrt sigma < 1.
  by rewrite -(ltr_sqr (sqrtr_ge0 _) ler01) sqr_sqrtr ?ltW // expr1n.
split; first by apply/andP; split.
have h : Num.sqrt sigma * Num.sqrt sigma < Num.sqrt sigma * 1.
  by rewrite (ltr_pM2l hq0).
by rewrite mulr1 -expr2 sqr_sqrtr ?ltW // in h.
Qed.

(** Source for [geometric_contraction_small]: the geometric power estimate
    supporting the last paragraph of Federer 2.8.2, p. 143. A fixed finite
    nonnegative bound times q^n eventually falls below every positive error
    when 0<q<1. *)
Lemma geometric_contraction_small (R : realType) (q a e : R) :
  0 < q < 1 -> 0 <= a -> 0 < e ->
  exists n : nat, q ^+ n * a < e.
Proof.
move=> /andP [hq0 hq1] ha he.
have hqi : 1 < q^-1 by rewrite invf_gt1.
have [n hn] := @geometric_powers_unbounded R q^-1 (a/e) hqi.
rewrite exprVn in hn.
have hp : 0 < q ^+ n by rewrite exprn_gt0.
have hpn : q ^+ n != 0 by rewrite (gt_eqF hp).
have hh : q ^+ n * (a/e) < q ^+ n * (q ^+ n)^-1.
  by rewrite (ltr_pM2l hp).
rewrite mulfV // in hh.
have heq : q ^+ n * (a/e) = (q ^+ n * a)/e by rewrite !mulrA.
rewrite heq (@ltr_pdivrMr R e 1 (q ^+ n * a) he) mul1r in hh.
by exists n.
Qed.

(** Source for [recurrent_contraction_small]: the vanishing error sequence
    in Federer 2.8.2, p. 143 Induction on the number of chosen contraction
    indices gives a_n <= q^k a_0 at some index, and monotonicity then gives
    the eventual error estimate. All terms are finite real numbers, as in
    the finite-measure reduction of the printed proof. *)
Theorem recurrent_contraction_small (R : realType) (q : R) (a : nat -> R) :
  0 < q < 1 -> (forall n, 0 <= a n) ->
  (forall n m, (n <= m)%N -> a m <= a n) ->
  (forall N, exists n, (N <= n)%N /\ a n.+1 <= q * a n) ->
  forall e, 0 < e -> exists N, forall n, (N <= n)%N -> a n < e.
Proof.
move=> hq hnon hmono hrec e he.
have hq0 : 0 < q := (andP hq).1.
have hbound k : exists n, a n <= q ^+ k * a 0%N.
  elim: k=> [|k [n hn]].
  - exists 0%N; by rewrite expr0 mul1r.
  - have [m [hnm hm]] := hrec n.
    have h1 : q * a m <= q * a n.
      rewrite (ler_pM2l hq0); exact: hmono n m hnm.
    have h2 : q * a n <= q * (q ^+ k * a 0%N).
      by rewrite (ler_pM2l hq0).
    have hb := le_trans hm (le_trans h1 h2).
    have heq : q * (q ^+ k * a 0%N) = q ^+ k.+1 * a 0%N.
      by rewrite exprS !mulrA.
    exists m.+1; by rewrite -heq.
have [k hk] := @geometric_contraction_small R q (a 0%N) e hq (hnon 0%N) he.
have [N hN] := hbound k; exists N=> n hNn.
exact: le_lt_trans (hmono N n hNn) (le_lt_trans hN hk).
Qed.
