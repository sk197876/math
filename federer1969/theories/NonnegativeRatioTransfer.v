(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


(** Source for [nonnegative_two_denominator_ratio_bound]: supporting
    finite scalar arithmetic for the final displayed estimate
    in Federer 2.9.17, p. 162. From a<=C e
    and d<=lambda b with positive denominators, infer
    a/b<=C lambda (e/d). This accounts for the third
    growth factor after the covering estimate. *)
Lemma nonnegative_two_denominator_ratio_bound (R : realType) (a b e d C lambda : R) :
  0<b -> 0<d -> 0<=e -> 0<=C -> a<=C*e -> d<=lambda*b ->
  a/b<=(C*lambda)*(e/d).
Proof.
move=> hb hd he hC ha hdb.
have hi : 0<=b^-1 by rewrite invr_ge0; exact: ltW hb.
have h1 := ler_wpM2r hi ha.
have h2 : d/b<=lambda by rewrite ler_pdivrMr.
have hcoeff : 0<=C*(e/d).
  apply: mulr_ge0 hC _; apply: divr_ge0 he (ltW hd).
have h3 := ler_wpM2l hcoeff h2.
have hd0 : d!=0 by rewrite (gt_eqF hd).
have heL : C*(e/d)*(d/b)=(C*e)/b.
  by rewrite !mulrA -[C*e*d^-1*d]mulrA mulVf // mulr1.
have heR : C*(e/d)*lambda=(C*lambda)*(e/d) by ring.
rewrite heL heR in h3; exact: le_trans h1 h3.
Qed.
