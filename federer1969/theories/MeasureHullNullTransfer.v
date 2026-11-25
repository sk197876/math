(** Null-set bookkeeping in Federer (1969), 2.9.11, p. 158: transfer a hull
    to an intermediate measurable set differing only on a null set. The
    lemmas use the existing measure, null-modification and hull laws; no
    regularity is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureHull
  MeasureNullModification MeasurableAlmostModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_agreeing_sets_difference_null]: supporting null
    symmetric-difference conclusions for P and its hull B in Federer 2.9.11,
    p. 158 *)
Lemma measure_agreeing_sets_difference_null (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B : set X) :
  is_measure phi -> measure_almost_everywhere phi [set x | A x <-> B x] -> phi (A `\` B)=0.
Proof.
move=> hm he; apply: (@measure_null_subset R X phi hm _ (~` [set x | A x <-> B x])) he.
move=> x [ha hn] hh; exact: hn (hh.1 ha).
Qed.

(** Source for [measure_agreeing_sets_intersection_value]: supporting
    null-invariance of the hull test intersections in Federer
    2.9.11, p. 158. The test T may be arbitrary and all
    three measure values may be infinite; no cancellation is used. *)
Lemma measure_agreeing_sets_intersection_value (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B T : set X) :
  is_measure phi -> measure_almost_everywhere phi [set x | A x <-> B x] ->
  phi (T `&` A)=phi (T `&` B).
Proof.
move=> hm he.
apply: (@measure_null_modification_value R X phi hm _ _ (~` [set x | A x <-> B x]) he)=> x hn.
have hx : A x <-> B x by apply: contrapT=> hab; exact: hn hab.
split=> [[ht ha]|[ht hb]]; split=> //; [exact: hx.1 ha|exact: hx.2 hb].
Qed.

(** Source for [measure_agreeing_sets_measurable]: supporting
    null-modification measurability in Federer 2.9.11, p. 158 The agreement
    set itself need not be assumed measurable; its complement is null. *)
Lemma measure_agreeing_sets_measurable (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B : set X) :
  is_measure phi -> measure_almost_everywhere phi [set x | A x <-> B x] ->
  measure_measurable phi A -> measure_measurable phi B.
Proof.
move=> hm he hA.
apply: (@measurable_set_null_modification R X phi hm A B (~` [set x | A x <-> B x]) he _ hA)=> x hn.
by apply: contrapT=> hab; exact: hn hab.
Qed.

(** Source for [measure_hull_agreement_transfer]: supporting hull transfer
    in Federer 2.9.11, p. 158: a containing set C almost equal to a hull B
    is again a hull. Every measurable test equality is retained explicitly. *)
Lemma measure_hull_agreement_transfer (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B C : set X) :
  is_measure phi -> is_measure_hull phi A B -> A `<=` C ->
  measure_almost_everywhere phi [set x | B x <-> C x] -> is_measure_hull phi A C.
Proof.
move=> hm hB hAC he; constructor=> //.
- exact (@measure_agreeing_sets_measurable R X phi B C hm he (measure_hull_measurable hB)).
- move=> T hT; rewrite (@measure_hull_test R X phi A B hB T hT).
  exact: measure_agreeing_sets_intersection_value hm he.
Qed.
