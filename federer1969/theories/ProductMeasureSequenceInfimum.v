(** Federer (1969), 2.6.1, pp. 114–115: the literal sequential infimum
    formula for the Cartesian product. Natural indices start at zero here;
    this merely reindexes the printed positive integers. Repeated rectangles
    and empty gaps are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover NonnegativeSum
  ProductMeasure ProductMeasureCoverUP CountableCostEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_sequence_cover_bound]: every
    sequence cover in Federer 2.6.1, pp. 114–115,
    bounds the product measure by its numerical sum of costs. *)
Lemma product_measure_sequence_cover_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X * Y)) (A : nat -> set X) (B : nat -> set Y) :
  (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) ->
  S `<=` (\bigcup_n (A n `*` B n)) ->
  product_measure ha hb S <= nonnegative_sum setT (fun n => alpha (A n) * beta (B n)).
Proof.
move=> hm hc.
apply: le_trans (@measure_indexed_cover R (X * Y)%type [the choiceType of (nat : Type)]
  (product_measure ha hb) (product_measure_is_measure ha hb) S setT (fun n => A n `*` B n)
  (countableP setT) hc) _.
apply: nonnegative_sum_mono=> n _; exact (@product_measure_rectangle_bound R X Y alpha beta ha hb (A n) (B n) (hm n).1 (hm n).2).
Qed.

(** Source for [product_measure_sequence_cover_greatest]: the
    greatest-lower-bound half of the exact sequential definition in Federer
    2.6.1, pp. 114–115 Zero-cost empty rectangles complete each countable
    cover to a sequence without changing its cost. *)
Lemma product_measure_sequence_cover_greatest (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) c :
  (forall (A : nat -> set X) (B : nat -> set Y),
    (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) ->
    S `<=` (\bigcup_n (A n `*` B n)) ->
    c <= nonnegative_sum setT (fun n => alpha (A n) * beta (B n))) ->
  c <= product_measure ha hb S.
Proof.
move=> hc; apply: (product_cover_greatest (product_measure_cover_specification ha hb))=> G hG hm hcover.
pose cost (p : set X * set Y) := alpha p.1 * beta p.2.
have hz : cost (set0,set0)=0 by rewrite /cost /= (measure_empty ha) mul0e.
have hpos p : G p -> 0 <= cost p.
  move=> _; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
have [u [hu [hen hsum]]] := countable_zero_cost_enumeration hG hz hpos.
rewrite -hsum; apply: (hc (fun n => (u n).1) (fun n => (u n).2)).
- move=> n; have [hp|he] := hu n; first exact: hm (u n) hp.
  rewrite he /=; split; exact: measure_measurable_empty.
- move=> p hp; have [q hq hpq] := hcover p hp; have [n hn] := hen q hq.
  exists n=> //; by rewrite hn.
Qed.
