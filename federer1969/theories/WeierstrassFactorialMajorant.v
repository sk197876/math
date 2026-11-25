(** Federer (1969), 3.4.6, p. 323: factorial
    growth of actual derivatives gives the original geometric
    growth of mixed divided coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import FactorialExponentialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_mixed_factorial_majorant]: the
    binomial estimate in 3.4.6, p. 323.
    The factor d absorbs the norm of the original
    direction, so no unit-direction hypothesis is imposed. *)
Lemma weierstrass_mixed_factorial_majorant (R:realType) (b t d u w:R) i j:
  0<=b ->0<=t ->1<=d ->0<=u ->u<=d ->0<=w ->w<=1 ->
  b*t^+(i+j)*((i+j)`!)%:R*u^+i*w^+j/((i`!)%:R*(j`!)%:R)<=
    b*(2*t*d)^+(i+j).
Proof.
move=>hb ht hd hu hud hw hw1.
have hd0:0<=d:=le_trans ler01 hd.
have hIF:((i`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hJF:((j`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hBinomial:(((i+j)`!)%:R:R)= 'C(i+j,i)%:R*((i`!)%:R*(j`!)%:R).
  have hi:(i<=i+j)%N by rewrite leq_addr.
  have hf:=bin_fact hi.
  have hSub:(i+j-i)%N=j by rewrite addnC addnK.
  rewrite hSub in hf.
  by rewrite -!natrM hf.
have hIdentity:b*t^+(i+j)*((i+j)`!)%:R*u^+i*w^+j/((i`!)%:R*(j`!)%:R)=
    ('C(i+j,i)%:R:R)*(b*t^+(i+j)*(u^+i*w^+j)).
  rewrite hBinomial;field;by rewrite hJF hIF.
rewrite hIdentity.
have hBin:('C(i+j,i)%:R:R)<=(2:R)^+(i+j).
  rewrite -natrX ler_nat;exact:binomial_power_two_bound.
have hUI:=lerXn2r i hu hd0 hud.
have hWJ:=lerXn2r j hw ler01 hw1.
rewrite expr1n in hWJ.
have hDJ:=lerXn2r j ler01 hd0 hd.
rewrite expr1n in hDJ.
have hProd:=le_trans (ler_wpM2r (exprn_ge0 j hw) hUI)
  (ler_wpM2l (exprn_ge0 i hd0) (le_trans hWJ hDJ)).
rewrite -exprD in hProd.
have hBase:=mulr_ge0 hb (exprn_ge0 (i+j)%N ht).
have hTerm:=mulr_ge0 hBase (mulr_ge0 (exprn_ge0 i hu) (exprn_ge0 j hw)).
have hFirst:=ler_wpM2r hTerm hBin.
have hSecond:=ler_wpM2l (exprn_ge0 (i+j)%N (ler0n R 2))
  (ler_wpM2l hBase hProd).
apply:le_trans (le_trans hFirst hSecond) _.
have hRight:(2:R)^+(i+j)*(b*t^+(i+j)*d^+(i+j))=b*(2*t*d)^+(i+j).
  by rewrite !exprMn;ring.
by rewrite hRight.
Qed.
