(** Federer (1969), 2.3.4, p. 76: elementary consequences of countable
    measurability. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureCountableClosure CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_set_measurable]: supporting consequence
    of Federer 2.3.4, p. 76, by 2.1.3(2), pp. 55–56 *)
Lemma countably_measurable_set_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) A :
  measure_countably_measurable mu A -> measure_measurable mu A.
Proof.
move=> [C [hc [-> hC]]].
apply: (@measure_measurable_countable_union R X [the choiceType of set X] mu hm C
  (fun B => B) hc)=> B hB; exact: (hC B hB).1.
Qed.

(** Source for [finite_measurable_set_countably_measurable]: supporting
    single-member-family case of Federer 2.3.4, p. 76 *)
Lemma finite_measurable_set_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) :
  measure_measurable mu A -> mu A < +oo -> measure_countably_measurable mu A.
Proof.
move=> ha hf; exists [set A]; split; first exact: countable1.
split.
- apply/seteqP; split=> x; [by move=> hx; exists A|by move=> [B ->]].
- by move=> B ->; split.
Qed.

(** Source for [empty_set_countably_measurable]: supporting empty
    family case of the first definition in Federer 2.3.4, p. 76. *)
Lemma empty_set_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) : measure_countably_measurable mu set0.
Proof.
exists set0; split; first exact: countable0.
split; last by move=> B [].
by rewrite bigcup_set0.
Qed.
