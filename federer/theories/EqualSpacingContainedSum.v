(** Federer (1969), 2.10.28(4), proof p. 193: bound the total cost of whole
    equal-cost children lying in a test interval by its concave length cost.
    Use the first and last selected child and the span inequality; the
    finite index count is at most last-first+1. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws EqualSpacingConcaveSpan
  EqualSpacingIntervalGeometry FiniteOrdinalSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_spacing_contained_sum_bound]: supporting
    whole-child cost bound proving Phi(J,n)
    special in 2.10.28(4), pp. 192–193.
    This is a consequence of concavity and
    finite spacing; it does not assume
    specialness or a mass bound for the
    resulting Cantor set. *)
Theorem equal_spacing_contained_sum_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) n (a d s t u v : R) :
  (2<=n)%N -> 0<d -> 0<s -> s<t ->
  h s=h d/n%:R -> t=(d-s)/(n%:R-1) -> u<=v ->
  \sum_(i : 'I_n | (u<=a+i%:R*t) && (a+i%:R*t+s<=v)) h s<=h (v-u).
Proof.
move=> hn hd hs hst hcost ht huv.
pose P (i : 'I_n) := (u<=a+i%:R*t) && (a+i%:R*t+s<=v).
change (\sum_(i : 'I_n | P i) h s<=h (v-u)).
case: (pselect (exists i, P i))=> [hP|hno]; last first.
  have hz : (\sum_(i : 'I_n | P i) h s)=0.
    apply: big1=> i hi; exfalso; apply: hno; by exists i.
  rewrite hz; apply: (@concave_interval_gauge_nonnegative R h hg (v-u)); by rewrite subr_ge0.
have [lo [hi [hlo [hhi hspan]]]] := @finite_ordinal_extremes n P hP.
have hlohi : (lo<=hi)%N := (hspan hi hhi).1.
pose p := (hi%:R-lo%:R : R).
have hp : 0<=p by rewrite /p subr_ge0 ler_nat.
have hhiN := @natural_index_real_upper_bound R (val hi) n (ltn_ord hi).
have hlo0 : (0<=lo%:R :> R) := @ler0n R (val lo).
have hpN : p<=n%:R-1 by rewrite /p; lra.
have hN1 : (1<n%:R :> R) by rewrite ltr1n.
have /andP[hul hlor] : (u<=a+lo%:R*t) && (a+lo%:R*t+s<=v) := hlo.
have /andP[huhi hhir] : (u<=a+hi%:R*t) && (a+hi%:R*t+s<=v) := hhi.
have ht0 : 0<=t by lra.
have hpt0 : 0<=p*t := mulr_ge0 hp ht0.
have hlen : p*t+s<=v-u by rewrite /p; lra.
have hlen0 : 0<=p*t+s by lra.
have hmono := @interval_gauge_increasing R h hg (p*t+s) (v-u) hlen0 hlen.
have hconc := @equal_spacing_concave_span_bound R h hg d s n%:R t p hd hs hN1 hp hpN hcost ht.
have hcard := @finite_ordinal_span_card n P (val lo) (val hi) hspan.
have hcardR : ((#|P|)%:R<=((val hi-val lo+1)%N)%:R :> R) by rewrite ler_nat.
have hrealcount : ((#|P|)%:R<=p+1 :> R).
  by move: hcardR; rewrite natrD (@natrB R (val hi) (val lo) hlohi).
have hhs : 0<=h s := concave_interval_gauge_nonnegative hg (ltW hs).
rewrite sumr_const -mulr_natl.
exact: le_trans (ler_wpM2r hhs hrealcount) (le_trans hconc hmono).
Qed.
