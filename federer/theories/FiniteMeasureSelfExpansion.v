(** Finite self-expansion in Federer (1969), 2.10.18(3), p. 181:
    (1+1/n)q<=q<infinity forces q=0. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_nonnegative_self_expansion_zero]: supporting
    cancellation in 2.10.18(3), p. 181 The essential finite upper bound
    excludes the infinite fixed point. *)
Lemma finite_nonnegative_self_expansion_zero (R : realType) (q : \bar R) (t : R) :
  0<=q -> q < +oo -> (1<t)%R -> t%:E*q<=q -> q=0.
Proof.
case: q=> [a| |] h0 hf ht hs //.
rewrite lee_fin in h0; rewrite -EFinM lee_fin in hs.
have [->|hne] := eqVneq a 0%R; first by [].
have ha : (0<a)%R by rewrite lt_def hne h0.
have hlt : (1*a<t*a)%R by rewrite (ltr_pM2r ha).
rewrite mul1r in hlt.
by have := lt_le_trans hlt hs; rewrite ltxx.
Qed.
