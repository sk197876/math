(** Federer (1969), 2.1.1(12), p. 53: a finite numerical sum has countable
    nonzero support. Here the terms are nonnegative. Source context:
    NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_finite_threshold_bound]: Federer 2.1.1(12), p.
    53; supporting bound: a finite set of terms each at least c contributes
    at least its cardinality times c. *)
Lemma nonnegative_finite_threshold_bound (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (B : {fset I}) (c : R) :
  (forall x, x \in B -> A x /\ c%:E <= f x) ->
  (#|` B|%:R * c)%:E <= nonnegative_sum A f.
Proof.
move=> hB; have hC : (#|` B|%:R * c)%:E = \sum_(x <- B) c%:E.
  by rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE mulr_natl cardE.
rewrite hC; apply: le_trans (_ : (\sum_(x <- B) f x) <= _).
- rewrite !big_seq; apply: lee_sum=> x hx; exact: (hB x hx).2.
- apply: nonnegative_sum_upper=> x hx; exact: (hB x hx).1.
Qed.

(** Source for [nonnegative_sum_threshold_finite]: Federer 2.1.1(12), p. 53;
    finiteness of every positive superlevel set when the total sum is
    finite. *)
Theorem nonnegative_sum_threshold_finite (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (c : R) :
  (0 < c)%R -> nonnegative_sum A f < +oo ->
  finite_set (A `&` [set x | c%:E <= f x]).
Proof.
move=> hc hs; apply: contrapT => hInf.
have hnon := nonnegative_sum_nonnegative A f.
case hval: (nonnegative_sum A f)=> [L| |].
- have hL : (0 <= L)%R by move: hnon; rewrite hval lee_fin.
  pose n := Num.bound (L / c).
  have hratio : (0 <= L / c)%R by apply: divr_ge0=> //; exact: ltW hc.
  have hlarge : (L < n%:R * c)%R.
    by rewrite -ltr_pdivrMr //; exact: archi_boundP hratio.
  have [B hB hn] := infinite_set_fset n hInf.
  have hbound := nonnegative_finite_threshold_bound (fun x hx => hB x hx).
  rewrite hval lee_fin in hbound.
  have hcard : (n%:R * c <= #|` B|%:R * c)%R.
    apply: ler_wpM2r; first exact: ltW hc.
    by rewrite ler_nat.
  have := lt_le_trans hlarge (le_trans hcard hbound); by rewrite ltxx.
- by move: hs; rewrite hval ltxx.
- by move: hnon; rewrite hval.
Qed.

(** Source for [nonnegative_sum_countable_support]: Federer 2.1.1(12), p.
    53, nonnegative case; the support lies in the countable union of the
    finite positive-threshold sets. *)
Theorem nonnegative_sum_countable_support (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (forall x, A x -> 0 <= f x) -> nonnegative_sum A f < +oo ->
  countable (A `&` [set x | f x != 0]).
Proof.
move=> hf hs.
pose F n := A `&` [set x | ((n.+1)%:R : R)^-1%:E <= f x].
have hFc : countable (\bigcup_n F n).
  apply: bigcup_countable; first exact: countableP.
  move=> n _; apply: finite_set_countable; apply: nonnegative_sum_threshold_finite hs.
  by rewrite invr_gt0 ltr0n.
have hsub : (A `&` [set x | f x != 0]) `<=` \bigcup_n F n.
  move=> x [hx hn]; have h0 := hf x hx.
  case he: (f x) => [r| |].
  - have hr : (0 < r)%R.
      move: h0; rewrite he lee_fin => h0.
      move: hn; rewrite /= he eqe => hn.
      by rewrite lt_def hn h0.
    pose n := Num.bound r^-1.
    have hnr : (r^-1 < n%:R)%R by apply: archi_boundP; rewrite invr_ge0; exact: ltW hr.
    exists n; first by [].
    split; first exact hx; rewrite /= he lee_fin invf_ple ?inE ?ltr0n //.
    + apply: le_trans (ltW hnr) _; by rewrite ler_nat.
    + change (0 < (n.+1%:R : R))%R; by rewrite ltr0n.
  - exists 0%N; first by [].
    split; first exact hx; rewrite /= he; exact: leey.
  - by move: h0; rewrite he.
exact: sub_countable (subset_card_le hsub) hFc.
Qed.
