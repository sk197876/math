(** Federer (1969), 3.2.13, p. 250: positive
    dyadic segments exhaust the defining Gamma ray.
    The concrete endpoints are local witnesses for
    the improper-integral proof, not a new chosen
    Gamma implementation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import GammaDyadicIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gamma_dyadic_origin_antitone]: decreasing
    positive endpoints for the Gamma ray exhaustion,
    supporting Federer 3.2.13, p. 250. *)
Lemma gamma_dyadic_origin_antitone (R:realType) n N:
  (n<=N)%N ->(1/2:R)^+N<=(1/2)^+n.
Proof.
move=>hnN.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<=1) by lra.
rewrite -(subnKC hnN) exprD.
have hSmall:((1/2:R)^+(N-n)<=1):=exprn_ile1 (N-n)%N (ltW hHalf) hHalf1.
have hh:=ler_wpM2l (exprn_ge0 n (ltW hHalf)) hSmall.
by rewrite mulr1 in hh.
Qed.

(** Source for [gamma_dyadic_tail_monotone]: increasing
    upper endpoints for the Gamma exhaustion,
    supporting Federer 3.2.13, p. 250. *)
Lemma gamma_dyadic_tail_monotone (R:realType) n N:
  (n<=N)%N ->(2:R)^+n<=2^+N.
Proof.
move=>hnN.
have hTwo:0<(2:R) by lra.
have hOne j:1<=(2:R)^+j.
  elim:j=>[|j ih]; first by rewrite expr0.
  rewrite exprS; nra.
rewrite -(subnKC hnN) exprD.
have hh:=ler_wpM2l (exprn_ge0 n (ltW hTwo)) (hOne (N-n)%N).
by rewrite mulr1 in hh.
Qed.

(** Source for [gamma_dyadic_segments_exhaust_positive]: every
    positive x eventually belongs to every later
    closed dyadic segment, supporting passage to
    the Gamma integral in Federer 3.2.13,
    p. 250. No endpoint at zero is used. *)
Lemma gamma_dyadic_segments_exhaust_positive (R:realType) (x:R):
  0<x ->exists N,forall n,(N<=n)%N ->(1/2)^+n<=x<=2^+n.
Proof.
move=>hx.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<=1) by lra.
have hOne j:1<=(2:R)^+j.
  elim:j=>[|j ih]; first by rewrite expr0.
  rewrite exprS; nra.
case:(leP x 1)=>hx1.
- have [N [hLow hHigh]]:=gamma_origin_intervals_cover hx hx1.
  exists N.+1=>n hn.
  have hStep:((1/2:R)^+N.+1=(1/2)^+N/2) by rewrite exprS mulrC div1r.
  have hLower:((1/2:R)^+n<=x).
    have hMono:((1/2:R)^+n<=(1/2)^+N.+1):=@gamma_dyadic_origin_antitone R N.+1 n hn.
    rewrite hStep in hMono; exact (le_trans hMono hLow).
  apply/andP; split=>//; exact:le_trans hx1 (hOne n).
- have [N [hLow hHigh]]:=gamma_tail_intervals_cover (ltW hx1).
  exists N.+1=>n hn.
  apply/andP; split.
  + apply:le_trans (exprn_ile1 n (ltW hHalf) hHalf1) _; exact:ltW hx1.
  + exact (le_trans hHigh (@gamma_dyadic_tail_monotone R N.+1 n hn)).
Qed.
