(** Federer (1969), 2.6.3(1), p. 117: the diagonal over [0,1] has infinite
    Lebesgue-times-counting product measure. The cover proof here works for
    any positive-measure set under an atomless measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureAlmostBasic CountingMeasure
  PositiveClosedSubsets PositiveCoverMember ProductMeasure ProductMeasureSequenceInfimum
  ProductAssociativityObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [atomless_counting_diagonal_infinite]: direct
    infinite-product-measure mechanism in Federer 2.6.3(1),
    p. 117, generalised from [0,1] to any positive
    set. Every countable rectangle cover has a positive
    diagonal overlap; its counting factor must be infinite. *)
Theorem atomless_counting_diagonal_infinite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  (forall x, mu [set x] = 0) -> 0 < mu A ->
  product_measure hm (counting_measure_is_measure R X) (restricted_diagonal A) = +oo.
Proof.
move=> hz hA; apply/eqP; rewrite eq_le leey /=.
apply: (product_measure_sequence_cover_greatest hm (counting_measure_is_measure R X))=> U V hUV hc.
pose D n := U n `&` V n.
have hcover : A `<=` \bigcup_n D n.
  move=> x hx; have [n _ [hU hV]] := hc (x,x) (conj hx erefl).
  by exists n=> //; split.
have [n hn] := @positive_countable_cover_member R X mu hm A D hA hcover.
have hU : 0 < mu (U n).
  apply: lt_le_trans hn _; apply: (measure_mono hm)=> x [hx _]; exact hx.
have hV : infinite_set (V n).
  move=> hf.
  have hv0 := @countable_null_singletons_null R X mu hm (V n) (finite_set_countable hf) (fun x _ => hz x).
  have hd0 : mu (D n) <= 0.
    rewrite -hv0; apply: (measure_mono hm)=> x [_ hx]; exact hx.
  by have := lt_le_trans hn hd0; rewrite ltxx.
have hv : mu (U n) * @counting_measure R X (V n) = +oo.
  by rewrite (@counting_measure_infinite R X (V n) hV) gt0_muley.
rewrite -hv; exact: nonnegative_sum_term Logic.I.
Qed.
