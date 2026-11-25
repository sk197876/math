(** This supports the local correction to the unrestricted associativity
    assertion in Federer 2.6.5, p. 119, using Federer's measure law in
    2.1.2, p. 53. The local erratum has no corresponding associativity
    correction *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_countable_cover_member]: Supporting Federer 2.6.5,
    p. 119.The covering sets need not be measurable. *)
Lemma positive_countable_cover_member (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (F : nat -> set X) :
  0 < mu A -> A `<=` \bigcup_n F n -> exists n, 0 < mu (F n).
Proof.
move=> hp hc; apply: contrapT=> hnone.
have hz n : mu (F n) = 0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
  apply/negP=> hn; apply: hnone; by exists n.
have hb := @measure_indexed_cover R X nat mu hm A setT F (countableP _) hc.
rewrite (nonnegative_sum_zero (fun n _ => hz n)) in hb.
by have := lt_le_trans hp hb; rewrite ltxx.
Qed.
