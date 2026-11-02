(** Federer (1969), proof of 2.4.6, p. 84: supporting removal of the common
    exceptional null set before applying the displayed finite-family
    assertion. Completeness of Caratheodory measurability makes every conull
    truth set measurable. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_conull_set_measurable]: supporting
    measurability of the common good set in Federer 2.4.6,
    p. 84, by 2.1.3(6), p. 55. *)
Lemma measure_conull_set_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : set X) :
  measure_almost_everywhere mu E -> measure_measurable mu E.
Proof.
move=> hE; have h := measure_measurable_complement (@measure_null_measurable R X mu hm (~` E) hE).
by rewrite setCK in h.
Qed.

(** Source for [measure_conull_intersection_value]: intersecting
    each finite test set with the common good set preserves its
    measure in the argument of Federer 2.4.6, p. 84. *)
Lemma measure_conull_intersection_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E A : set X) :
  measure_almost_everywhere mu E -> mu (A `&` E) = mu A.
Proof.
move=> hE; apply: (@measure_null_modification_value R X mu hm _ _ (~` E) hE)=> x hn.
have hx : E x by apply: contrapT=> h; exact: hn.
split; first by move=> [ha _].
move=> ha; by split.
Qed.
