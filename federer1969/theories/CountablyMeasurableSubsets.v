(** Federer (1969), 2.3.4, p. 76: a measurable subset of a countably
    measurable set is countably measurable. This supports subsequent
    restrictions of the nonzero locus. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure CountablyMeasurableUP CountablyMeasurableBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_subset_countably_measurable]: supporting
    restriction consequence of Federer 2.3.4, p. 76,
    by intersecting the finite-measure family with the measurable subset.
    This does not assert closure under arbitrary nonmeasurable subsets. *)
Lemma measurable_subset_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  measure_measurable mu A -> A `<=` B -> measure_countably_measurable mu B ->
  measure_countably_measurable mu A.
Proof.
move=> hA hAB [C [hc [he hC]]].
exists ((fun D => A `&` D) @` C); split.
- exact: sub_countable (card_image_le _ _) hc.
- split.
  + apply/seteqP; split=> x.
    * move=> hx; have hb := hAB x hx; rewrite he in hb; have [D hD hdx] := hb.
      exists (A `&` D); first by exists D.
      by split.
    * by move=> [D [E hE <-] [hx _]].
  + move=> D [E hE <-]; split.
    * exact: (@measure_measurable_intersection R X mu hm _ _ hA (hC E hE).1).
    * apply: le_lt_trans _ (hC E hE).2.
      apply: (@measure_mono R X mu hm)=> x [_ hx]; exact hx.
Qed.

(** Source for [null_set_countably_measurable]: supporting
    null-set case of Federer 2.3.4, p. 76, by the
    null-set measurability law of 2.1.3(6), p. 55. *)
Lemma null_set_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  mu A = 0 -> measure_countably_measurable mu A.
Proof.
move=> ha; apply: finite_measurable_set_countably_measurable.
- exact: (@measure_null_measurable R X mu hm A ha).
- rewrite ha; exact: ltry.
Qed.
