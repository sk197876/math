(** Supporting Federer (1969), 2.10.46, p. 204: a measure bounded by the
    product costs of Borel rectangles is bounded by the Cartesian product
    measure. Borel regular factor measures permit Borel covers in the
    infimum of 2.6.1, pp. 114–115. This is the existing covering comparison,
    not an assumed product identity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum
  BorelRegularMeasureUP TopologicalBorel ProductMeasure ProductBorelCoverApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_bounded_by_borel_product_rectangles]:
    supporting passage from Borel rectangle bounds to all
    subsets in the product argument of 2.10.46, p. 204,
    using the defining covering infimum in 2.6.1. *)
Theorem measure_bounded_by_borel_product_rectangles (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (mu : set (X*Y) -> \bar R) :
  is_borel_regular_measure alpha -> is_borel_regular_measure beta -> is_measure mu ->
  (forall A B, borel_set A -> borel_set B -> mu (A `*` B)<=alpha A*beta B) ->
  forall S, mu S<=product_measure ha hb S.
Proof.
move=> hra hrb hm hrect S; rewrite leNgt; apply/negP=> hbad.
have [A [B [hAB [hcover hcost]]]] :=
  @product_measure_borel_cover_approximation R X Y alpha beta ha hb hra hrb S (mu S) hbad.
have hcov := @measure_indexed_cover R (X*Y)%type [the choiceType of (nat : Type)] mu hm S setT
  (fun j=>A j `*` B j) (countableP setT) hcover.
have hsum : nonnegative_sum setT (fun j=>mu (A j `*` B j))<=
    nonnegative_sum setT (fun j=>alpha (A j)*beta (B j)).
  apply: nonnegative_sum_mono=> j _; exact: hrect (hAB j).1 (hAB j).2.
by have hh := le_lt_trans (le_trans hcov hsum) hcost; rewrite ltxx in hh.
Qed.
