(** Federer (1969), 3.1.24, p. 238: a uniform
    geometric remainder tends to zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RecurrentContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_uniform_tail]: supporting uniform
    convergence of the Taylor remainder in Federer 3.1.24,
    p. 238. The previously proved small geometric
    power and monotonicity give one threshold for all later indices. *)
Lemma geometric_uniform_tail (R:realType) (q M eps:R) :
  0<q<1 -> 0<=M -> 0<eps ->
  exists n:nat,forall N,(n<=N)%N -> q^+N*M<eps.
Proof.
move=>hq hM heps; have [n hn]:=geometric_contraction_small hq hM heps.
exists n=>N hN.
have hp:q^+N<=q^+n.
  rewrite -(subnKC hN) exprD.
  have hh:=ler_wpM2l (exprn_ge0 n (ltW (andP hq).1))
    (exprn_ile1 (N-n)%N (ltW (andP hq).1) (ltW (andP hq).2)).
  by rewrite mulr1 in hh.
exact (le_lt_trans (ler_wpM2r hM hp) hn).
Qed.
