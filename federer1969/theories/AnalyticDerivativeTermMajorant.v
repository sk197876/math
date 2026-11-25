(** Federer (1969), 3.1.24, p. 238: the
    geometric majorant for the differentiated homogeneous terms. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import FactorialExponentialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_derivative_term_majorant]: supporting
    the displayed estimate m!/(m-i)! <= 2^m i! in
    Federer 3.1.24, p. 238. For a coefficient
    bounded by c^m m!, the ith derivative on a
    radius-s ball is majorised by (2c)^i i! (2cs)^(m-i).
    Both scalar parameters may be zero, and i=0 is included. *)
Lemma analytic_derivative_term_majorant (R:realType) m i (c s:R) :
  (i<=m)%N -> 0<=c -> 0<=s ->
  (c^+m*(m`!)%:R)*(s^+(m-i)/((m-i)`!)%:R)<=
    ((2*c)^+i*(i`!)%:R)*(2*c*s)^+(m-i).
Proof.
move=>hi hc hs.
have hd:(((m-i)`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hf:((m`!)%:R:R)= 'C(m,i)%:R*((i`!)%:R*((m-i)`!)%:R).
  by rewrite -!natrM bin_fact.
have heq:(c^+m*(m`!)%:R)*(s^+(m-i)/((m-i)`!)%:R)=
    'C(m,i)%:R*(c^+m*(i`!)%:R*s^+(m-i)).
  rewrite hf; field; exact hd.
rewrite heq.
have hbin:('C(m,i)%:R:R)<=(2:R)^+m.
  rewrite -natrX ler_nat; exact: binomial_power_two_bound.
have hp:0<=c^+m*(i`!)%:R*s^+(m-i).
  exact (mulr_ge0 (mulr_ge0 (exprn_ge0 m hc) (ler0n _ _)) (exprn_ge0 (m-i) hs)).
apply: le_trans (ler_wpM2r hp hbin) _.
have hex:(2*c)^+m= (2*c)^+i*(2*c)^+(m-i).
  by rewrite -exprD subnKC.
have hid:(2:R)^+m*(c^+m*(i`!)%:R*s^+(m-i))=
    ((2*c)^+i*(i`!)%:R)*(2*c*s)^+(m-i).
  have hl:(2:R)^+m*(c^+m*(i`!)%:R*s^+(m-i))=
      (2*c)^+m*(i`!)%:R*s^+(m-i) by rewrite exprMn; ring.
  rewrite hl hex [(2*c*s)^+(m-i)]exprMn; ring.
by rewrite hid.
Qed.
