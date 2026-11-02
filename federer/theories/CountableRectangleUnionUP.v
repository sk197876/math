(** Federer (1969), 2.6.2, p. 116: P1 consists of countable unions of
    measurable rectangles. We use sequences, allowing repeated and empty
    rectangles, and prove the countable-family equivalence separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureCountableClosure
  ProductMeasure ProductRectangleMeasurability ProductSections RectangleSectionIntegral CountableDefaultEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_countable_rectangle_union]: direct P1
    membership in Federer 2.6.2, p. 116, specified by
    existence of a measurable rectangle sequence with this union. *)
Definition is_countable_rectangle_union (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (S : set (X * Y)) :=
  exists (A : nat -> set X) (B : nat -> set Y),
    (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) /\
    S = \bigcup_n (A n `*` B n).

(** Source for [countable_rectangle_family_union]: supporting
    equivalence of countable families and the sequential P1
    definition in Federer 2.6.2, p. 116; empty rectangles
    fill missing indices and preserve the empty-family case. *)
Lemma countable_rectangle_family_union (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (G : set (set X * set Y)) :
  countable G -> (forall p, G p -> measure_measurable alpha p.1 /\ measure_measurable beta p.2) ->
  is_countable_rectangle_union alpha beta (\bigcup_(p in G) (p.1 `*` p.2)).
Proof.
move=> hc hm; have [u [hu hen]] := countable_default_enumeration (set0,set0) hc.
exists (fun n => (u n).1), (fun n => (u n).2); split.
- move=> n; have [hp|he] := hu n; first exact: hm (u n) hp.
  rewrite he /=; split; exact: measure_measurable_empty.
- apply/seteqP; split.
  + move=> z [p hp hzp]; have [n hn] := hen p hp; exists n=> //; by rewrite hn.
  + move=> z [n _ hz]; have [hp|he] := hu n; first by exists (u n).
    by rewrite he in hz; have [] := hz.1.
Qed.

(** Source for [countable_rectangle_union_measurable]: the
    measurability of P1 after proving rectangle measurability
    in Federer 2.6.2, pp. 116–117. *)
Lemma countable_rectangle_union_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  is_countable_rectangle_union alpha beta S -> measure_measurable (product_measure ha hb) S.
Proof.
move=> [A [B [hm ->]]]; apply: (measure_measurable_sequence_union (product_measure_is_measure ha hb))=> n.
exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb (A n) (B n) (hm n).1 (hm n).2).
Qed.

(** Source for [countable_rectangle_union_sections_measurable]:
    supporting section measurability for P1 in Federer 2.6.2,
    p. 116; countable unions commute with taking sections. *)
Lemma countable_rectangle_union_sections_measurable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (hb : is_measure beta) (S : set (X * Y)) :
  is_countable_rectangle_union alpha beta S ->
  forall x, measure_measurable beta (product_vertical_section S x).
Proof.
move=> [A [B [hm ->]]] x; rewrite product_vertical_union.
apply: (measure_measurable_sequence_union hb)=> n.
exact (@rectangle_vertical_section_measurable R X Y beta hb (A n) (B n) (hm n).2 x).
Qed.
