(** Federer (1969), 2.4.16, p. 90: choosing the first finite
    positive-measure set inside a positive superlevel set. This supporting
    lemma isolates the countable-measurability argument, including a
    possibly infinite measure of the ambient set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_countably_measurable_finite_subset]:
    supporting choice of A1 in Federer 2.4.16, p. 90,
    after the second integral display. *)
Lemma positive_countably_measurable_finite_subset (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  measure_countably_measurable mu A -> 0 < mu A ->
  exists B, B `<=` A /\ measure_measurable mu B /\ 0 < mu B /\ mu B < +oo.
Proof.
move=> hA hpos; have [C [he hC]] := (countably_measurable_sequence_iff hm A).1 hA.
have hn : exists n, mu (C n) <> 0.
  apply: contrapT=> hnone.
  have hz n : mu (C n) = 0 by apply: contrapT=> h; apply: hnone; exists n.
  have hh := @measure_null_countable_union R X (Choice.clone nat _) mu hm setT C
    (countableP _) (fun n _ => hz n).
  by move: hpos; rewrite he hh ltxx.
have [n hne] := hn; exists (C n); split.
- move=> x hx; rewrite he; by exists n.
split; first exact (hC n).1.
split; last exact (hC n).2.
have hne0 : mu (C n) != 0 by apply/eqP.
by rewrite lt_neqAle eq_sym hne0 (measure_nonnegative hm).
Qed.
