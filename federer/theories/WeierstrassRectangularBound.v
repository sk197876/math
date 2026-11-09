(** Federer (1969), 3.4.6, p. 323: the
    original rectangular geometric sum is bounded by
    the product of the two printed inverse gaps. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import WeierstrassGeometricPrefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_rectangular_geometric_bound]:
    the product [1-u] inverse [1-w] inverse bounds
    every original finite rectangle, supporting the
    shifted-series estimate in 3.4.6, p. 323.
    Both empty ranges and both zero ratios are retained. *)
Theorem weierstrass_rectangular_geometric_bound (R:realType) (D u w:R) I J:
  0<=D ->0<=u ->u<1 ->0<=w ->w<1 ->
  (\sum_(i<I) \sum_(j<J) D*u^+i*w^+j)<=D/(1-u)/(1-w).
Proof.
move=>hD hu hu1 hw hw1.
have hSumW:0<=\sum_(j<J) w^+j.
  apply:sumr_ge0=>j _.
  have hh:0<=w^+j:=exprn_ge0 j hw.
  exact:hh.
have hInner (i:'I_I):(\sum_(j<J) D*u^+i*w^+j)=(D*u^+i)*(\sum_(j<J) w^+j).
  by rewrite mulr_sumr.
have hFactor:(\sum_(i<I) \sum_(j<J) D*u^+i*w^+j)=D*(\sum_(i<I) u^+i)*(\sum_(j<J) w^+j).
  under eq_bigr do rewrite hInner.
  by rewrite -mulr_suml -mulr_sumr.
rewrite hFactor.
have hGap:0<=1/(1-u) by rewrite divr_ge0 // subr_ge0;exact:ltW hu1.
have hFirst:=ler_wpM2r hSumW (ler_wpM2l hD (@weierstrass_geometric_prefix R u I hu hu1)).
have hSecond:=ler_wpM2l (mulr_ge0 hD hGap) (@weierstrass_geometric_prefix R w J hw hw1).
apply:le_trans hFirst _;apply:le_trans hSecond _.
have hIdentity:D*(1/(1-u))*(1/(1-w))=D/(1-u)/(1-w) by ring.
by rewrite hIdentity.
Qed.
