(** Federer (1969), 3.2.18, p. 255:
    a positive part of a Lipschitz image
    meets one near-isometric piece in positive
    mass. This is the elementary countable-cover
    step between 3.2.4 and 3.2.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_countable_cover_piece]:
    some member of the countable image
    cover has positive mass in a
    positive remainder, supporting Federer 3.2.18,
    p. 255. The exceptional part of
    the original image may be null. *)
Lemma positive_countable_cover_piece (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (A U : set X) (D : set J) (F : J -> set X) :
  is_measure mu -> countable D -> mu (U `\` (\bigcup_(j in D) F j))=0 ->
  0<mu (A `&` U) -> exists j, D j /\ 0<mu (A `&` F j).
Proof.
move=> hm hCount hNull hPos.
case: (pselect (exists j, D j /\ 0<mu (A `&` F j)))=> hh; first exact hh.
have hZero j (hj : D j) : mu (A `&` F j)=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
  apply/negP=> hp; apply: hh; exists j; by split.
have hUnion := @measure_null_countable_union R X J mu hm D
  (fun j=>A `&` F j) hCount hZero.
have hCover : A `&` U `<=`
    (U `\` (\bigcup_(j in D) F j)) `|` (\bigcup_(j in D) (A `&` F j)).
  move=> x [hxA hxU]; case: (pselect ((\bigcup_(j in D) F j) x))=> hMem.
  - have [j hj hxj] := hMem; right; exists j=> //; by split.
  - left; by split.
have hb := measure_binary_cover hm hCover; rewrite hNull hUnion add0e in hb.
by have := lt_le_trans hPos hb; rewrite ltxx.
Qed.
