(** Finite self-contraction in the proof of Federer (1969), 2.10.17(3), p.
    179: a finite nonnegative value bounded by (1-delta) times itself must
    be zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_nonnegative_self_contraction_zero]: supporting
    numerical inference in 2.10.17(3), p. 179 Finiteness is essential:
    infinity is not forced to zero by multiplication by a positive number
    below one. *)
Lemma finite_nonnegative_self_contraction_zero (R : realType) (q : \bar R) (t : R) :
  0<=q -> q < +oo -> (t<1)%R -> q<=t%:E*q -> q=0.
Proof.
case: q=> [a| |] h0 hf ht hs //.
rewrite lee_fin in h0; rewrite -EFinM lee_fin in hs.
have [->|hne] := eqVneq a 0%R; first by [].
have ha : (0<a)%R by rewrite lt_def hne h0.
have hlt : (t*a<1*a)%R by rewrite (ltr_pM2r ha).
rewrite mul1r in hlt.
by have := lt_le_trans hlt hs; rewrite ltxx.
Qed.
