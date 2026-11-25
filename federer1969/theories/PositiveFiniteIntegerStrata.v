(** Federer (1969), 3.3.18, p. 301: the printed positive
    integer density bands cover every positive finite original density. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_finite_integer_stratum]: the countable
    exhaustion by i inverse < Theta* < i in Federer 3.3.18,
    p. 301. Choose an integer larger than both the positive
    finite value and its reciprocal, using only the actual
    Archimedean real-field background. Index zero denotes i=1. *)
Lemma positive_finite_integer_stratum (R : realType) (x : \bar R) :
  0<x< +oo ->exists i:nat,((i.+1)%:R:R)^-1%R%:E<x<((i.+1)%:R:R)%:E.
Proof.
case:x=>[r| |].
- move=>/andP[hPositive _].
  have hr:(0<r)%R:=hPositive.
  have hInv:(0<r^-1)%R by rewrite invr_gt0.
  pose M:=(Num.max r r^-1)%R.
  have hrM:(r<=M)%R by rewrite /M le_max lexx.
  have hInvM:(r^-1<=M)%R by rewrite /M le_max lexx orbT.
  have hM:(0<=M)%R:=le_trans (ltW hr) hrM.
  have hBound:(M<(Num.bound M)%:R)%R:=archi_boundP hM.
  have hBoundNext:(M<((Num.bound M).+1)%:R)%R.
    apply:lt_le_trans hBound _; by rewrite ler_nat.
  have hUpper:(r<((Num.bound M).+1)%:R)%R:=le_lt_trans hrM hBoundNext.
  have hInverse:(r^-1<((Num.bound M).+1)%:R)%R:=le_lt_trans hInvM hBoundNext.
  exists (Num.bound M); apply/andP; split; last by rewrite lte_fin.
  rewrite lte_fin -[r in (_<r)%R]invrK ltf_pV2 ?posrE ?ltr0n //.
- by rewrite ltxx andbF.
- move=>/andP[hImpossible _].
  by have:=lt_le_trans hImpossible (leNye 0); rewrite ltxx.
Qed.
