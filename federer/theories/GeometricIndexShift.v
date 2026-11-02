(** Federer (1969), 3.1.24, p. 238: bookkeeping
    for the lower index m=i in the derivative series. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_index_shift_factor]: supporting the
    geometric summation in Federer 3.1.24, p. 238.
    Expressing q^(m-i) as a multiple of q^m lets
    every derivative series use the original partial-sum indices.
    The nonzero condition is supplied by 0<q<1. *)
Lemma geometric_index_shift_factor (K:fieldType) (a b q:K) m i :
  q!=0 -> (i<=m)%N ->
  a^+i*b*q^+(m-i)= q^+m*((a/q)^+i*b).
Proof.
move=>hq hi.
have hm:q^+m= q^+i*q^+(m-i) by rewrite -exprD subnKC.
rewrite hm exprMn exprVn.
field; exact: expf_neq0.
Qed.
