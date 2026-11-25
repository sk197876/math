(** Federer (1969), 1.10.5, p. 48: local boundary correction to the infimum
    over finite sums of products of m vectors. In degree zero, each empty
    product equals one, so such unweighted sums cannot represent a negative
    scalar. The degree-zero mass uses absolute value separately. This is a
    local boundary clarification, not an entry in the saved Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded SymmetricAlgebra SymmetricGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_empty_product_sum_augmentation]: Federer
    1.10.5, p. 48, supporting calculation for the zero-degree
    exception: the augmentation of a sum of N empty products is N. *)
Lemma symmetric_empty_product_sum_augmentation (K : fieldType) (V : lmodType K) N :
  symmetric_augmentation V (\sum_(i : 'I_N) symmetric_word ([::] : seq V)) = (N%:R : K).
Proof.
rewrite linear_sum.
under eq_bigr do rewrite symmetric_word_nil symmetric_augmentation_unit.
by rewrite sumr_const card_ord.
Qed.

(** Source for [symmetric_negative_unit_not_empty_sum]: Federer
    1.10.5, p. 48, counterexample to extending the unweighted
    decomposition formula to m=0. The negative unit is not any finite
    sum of empty products over a real-closed scalar field. *)
Theorem symmetric_negative_unit_not_empty_sum (R : rcfType) (V : lmodType R) N :
  \sum_(i : 'I_N) symmetric_word ([::] : seq V) != - symmetric_unit V.
Proof.
apply/eqP=> h.
have ha := congr1 (symmetric_augmentation V) h.
rewrite symmetric_empty_product_sum_augmentation linearN symmetric_augmentation_unit in ha.
have hn : (0 : R) <= -1 by rewrite -ha; exact: ler0n.
have hf := lt_le_trans (@ltrN10 R) hn.
by rewrite ltxx in hf.
Qed.
