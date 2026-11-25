(** Federer (1969), 2.1.1(13), p. 53,
    used for the exact mass in
    4.1.12, p. 369: finite
    real prefixes converge to the real
    value of a finite nonnegative numerical sum.
    Apply the previously proved exact tails. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeRealSeriesTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_real_series_prefix_convergence]:
    every original finite-prefix scalar sum converges
    in absolute value to the finite
    original numerical sum, supporting M(S)=2
    sum k^(-2) in Federer 4.1.12,
    p. 369. No external series
    convergence theorem is used. *)
Theorem nonnegative_real_series_prefix_convergence (R:realType) (a:nat->R):
  (forall k,0<=a k)->(nonnegative_sum setT (fun k=>(a k)%:E)< +oo)%E->
  forall epsilon:R,0<epsilon->exists N,forall k,(N<=k)%N->
    `|(\sum_(j<k) a j)-fine (nonnegative_sum setT (fun j=>(a j)%:E))|<epsilon.
Proof.
move=>ha hFinite epsilon hEpsilon.
have[N hN]:=@nonnegative_real_series_tail_small R a ha hFinite epsilon hEpsilon.
exists N=>k hNk.
have hNumber:nonnegative_sum setT (fun j=>(a j)%:E) \is a fin_num.
  rewrite ge0_fin_numE;last exact:nonnegative_sum_nonnegative.
  exact:hFinite.
have hEquation:=@nonnegative_real_series_prefix_tail R a ha hFinite k.
rewrite -(fineK hNumber) in hEquation.
have hReal:=EFin_inj hEquation.
rewrite hReal opprD addrA subrr add0r normrN.
rewrite (ger0_norm (@nonnegative_real_series_tail_nonnegative R a hFinite k)).
exact:hN k hNk.
Qed.
