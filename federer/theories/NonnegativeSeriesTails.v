(** Federer (1969), 2.3.2(7), p. 75, after the even/odd band estimate: a
    finite nonnegative series has arbitrarily small tails. This supporting
    consequence of 2.1.1(13), p. 53, is proved from the project's abstract
    sum and order-limit laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction NonnegativeSumContinuity
  ExtendedRealOrderLimit ExtendedRealDifferenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_series_tail_limit]: supporting vanishing-tail
    fact used in Federer 2.3.2(7), p. 75. The series is the local abstract
    nonnegative sum, not an imported summability predicate. *)
Theorem nonnegative_series_tail_limit (R : realType) (a : nat -> \bar R) :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo ->
  extended_order_limit (fun N => nonnegative_sum [set n | (N <= n)%N] a) 0.
Proof.
move=> ha hs; pose S := nonnegative_sum setT a.
pose P N := nonnegative_sum [set n | (n < N)%N] a.
have hS0 : 0 <= S := nonnegative_sum_nonnegative setT a.
have hSf : S \is a fin_num by rewrite ge0_fin_numE.
have hPbound N : P N <= S.
  apply: nonnegative_sum_subset=> n hn; exact Logic.I.
have hPf N : P N \is a fin_num.
  rewrite ge0_fin_numE; last exact: nonnegative_sum_nonnegative.
  exact: le_lt_trans (hPbound N) hs.
have hlim : extended_order_limit P S.
  apply: (proj2 (@nonnegative_sum_increasing_limit R nat setT
    (fun N => [set n | (n < N)%N]) a _ _ _)).
  - move=> N M hNM n hn; exact: leq_trans hn hNM.
  - by move=> N n hn.
  - move=> n _; exists n.+1; exact: ltnSn.
have hdiff N : S - P N = nonnegative_sum [set n | (N <= n)%N] a.
  have he : setT `\` [set n | (n < N)%N] = [set n | (N <= n)%N].
    apply/seteqP; split=> n.
    + move=> [_ hn]; change (N <= n)%N; rewrite leqNgt; exact/negP.
    + move=> hn; have hn' : (N <= n)%N := hn; split; first exact Logic.I.
      move=> hlt; by move: hn'; rewrite leqNgt hlt.
  rewrite /S (@nonnegative_sum_split R nat setT [set n | (n < N)%N] a).
  - rewrite setTI he /P [nonnegative_sum _ _ + nonnegative_sum _ _]addeC addeK //; exact: hPf.
  - by move=> n _; exact: ha.
have hconst : extended_order_limit (fun _ : nat => S) S.
  split=> b hb; exists 0%N=> n hn; exact hb.
have hfin : (S < +oo) || (S < +oo) by rewrite hs.
have hresult := @extended_nonnegative_difference_limit R (fun _ => S) P S S
  hS0 hS0 hfin (fun _ => lexx _) hPbound hconst hlim.
have he : (fun N => S - P N) = (fun N => nonnegative_sum [set n | (N <= n)%N] a).
  apply: funext=> N; exact: hdiff.
by rewrite he subee in hresult.
Qed.

(** Source for [nonnegative_series_tail_small]: direct supporting
    epsilon-tail estimate used in Federer 2.3.2(7), p. 75, after bounding
    the band series *)
Corollary nonnegative_series_tail_small (R : realType) (a : nat -> \bar R) (eps : R) :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo -> (0 < eps)%R ->
  exists N, nonnegative_sum [set n | (N <= n)%N] a < eps%:E.
Proof.
move=> ha hs he; have hlim := @nonnegative_series_tail_limit R a ha hs.
have hp : 0 < eps%:E by rewrite lte_fin.
have [N hN] := hlim.2 eps%:E hp; exists N; exact: hN N (leqnn N).
Qed.
