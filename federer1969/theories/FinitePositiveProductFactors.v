(** Federer (1969), 2.6.4, pp. 118–119: supporting reduction of
    finite-measure rectangles to finite factor measures, except for null
    rectangles. This is needed in the printed successive P0,P1,P2 density
    argument. It uses the convention zero times infinity equals zero in
    2.1.1, p. 53. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [positive_finite_product_factors]: supporting
    scalar reduction for the rectangle density step in Federer
    2.6.4, pp. 118–119. The positive-product premise is
    essential: zero times infinity is zero in the book's convention. *)
Lemma positive_finite_product_factors (R : realType) (a b : \bar R) :
  0 <= a -> 0 <= b -> 0 < a*b -> a*b < +oo ->
  0 < a /\ a < +oo /\ 0 < b /\ b < +oo.
Proof.
move=> ha hb hp hf.
have ha0 : a != 0 by apply/eqP=> he; move: hp; by rewrite he mul0e ltxx.
have hb0 : b != 0 by apply/eqP=> he; move: hp; by rewrite he mule0 ltxx.
have hap : 0 < a by rewrite lt_neqAle eq_sym ha0 ha.
have hbp : 0 < b by rewrite lt_neqAle eq_sym hb0 hb.
have haf : a < +oo.
  case he: a ha hf=> [r| |] ha' hf'; rewrite ?ltry ?ltNyy //.
  move: hf'; by rewrite muleC gt0_muley // ltxx.
have hbf : b < +oo.
  case he: b hb hf=> [r| |] hb' hf'; rewrite ?ltry ?ltNyy //.
  move: hf'; by rewrite gt0_muley // ltxx.
by split=> //; split=> //; split.
Qed.
