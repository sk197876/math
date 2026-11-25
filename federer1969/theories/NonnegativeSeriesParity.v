(** Federer (1969), 2.3.2(7), p. 75: finite parity-band estimates bound the
    whole nonnegative series by twice the measure of the test set. These
    supporting summation lemmas use the local abstract sum, covering and
    order-limit laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumContinuity NonnegativeSumCover
  NonnegativeSumImageBound NonnegativeSumBoolean ExtendedRealOrderLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_series_prefix_bound]: supporting
    passage from finite prefixes to a series bound in Federer
    2.3.2(7), p. 75, using 2.1.1(13), p. 53. *)
Lemma nonnegative_series_prefix_bound (R : realType) (a : nat -> \bar R) b :
  (forall N, nonnegative_sum [set n | (n < N)%N] a <= b) -> nonnegative_sum setT a <= b.
Proof.
move=> hb.
have hlim : extended_increases_to (fun N => nonnegative_sum [set n | (n < N)%N] a)
    (nonnegative_sum setT a).
  apply: (@nonnegative_sum_increasing_limit R nat setT _ a).
  - move=> N M hNM n hn; exact: leq_trans hn hNM.
  - by move=> N n hn.
  - move=> n _; exists n.+1; exact: ltnSn.
exact: (@extended_order_limit_upper_bound R _ _ b hlim.2 hb).
Qed.

(** Source for [nonnegative_series_parity_bound]: supporting combination of
    the even and odd bounds in Federer 2.3.2(7), p. 75 The result is an
    upper bound; no disjointness assumption on any underlying sets is used. *)
Lemma nonnegative_series_parity_bound (R : realType) (a : nat -> \bar R) b :
  (forall n, 0 <= a n) ->
  (forall p : bool, nonnegative_sum setT (fun n => a (n.*2 + p)%N) <= b) ->
  nonnegative_sum setT a <= b + b.
Proof.
move=> ha hb.
pose F (p : bool) := (fun n : nat => (n.*2 + p)%N) @` setT.
have hcover : setT `<=` \bigcup_(p in (@setT bool)) F p.
  move=> n _; exists (odd n); first exact Logic.I.
  exists n./2; first exact Logic.I.
  by rewrite addnC odd_double_half.
have h := @nonnegative_sum_cover R nat bool setT setT F a ha hcover.
apply: le_trans h _.
have hh : nonnegative_sum setT (fun p => nonnegative_sum (F p) a) <=
    nonnegative_sum setT (fun p : bool => nonnegative_sum setT (fun n => a (n.*2+p)%N)).
  apply: nonnegative_sum_mono=> p _.
  apply: nonnegative_sum_image_bound=> n _; exact: ha.
apply: le_trans hh _.
rewrite nonnegative_sum_bool; last by move=> p; exact: nonnegative_sum_nonnegative.
exact: leeD (hb true) (hb false).
Qed.
