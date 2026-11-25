(** Federer (1969), 2.5.10, pp. 100–101: transferring the local density on a
    measurable piece to the original measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_restriction_intersection_transfer]: supporting
    local-to-global measurability in Federer 2.5.10, pp. 100–101 Unlike the
    classification in 2.1.5(5), no regularity or finite-measure premise is
    needed when the restricting set is measurable. *)
Lemma measurable_restriction_intersection_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B E : set X) :
  measure_measurable mu B -> measure_measurable (measure_restrict mu B) E ->
  measure_measurable mu (E `&` B).
Proof.
move=> hB hE; apply/(measure_measurable_finite_test hm)=> T hT.
have hi : B `&` (T `&` E)=T `&` (E `&` B).
  apply/seteqP; split=> [x [hb [ht he]]|x [ht [he hb]]]; by split=> //; split.
have hd : B `&` (T `\` E)=(T `&` B) `\` E.
  apply/seteqP; split=> [x [hb [ht hn]]|x [[ht hb] hn]]; by split=> //; split.
have hs := hE T; rewrite /measure_restrict setIC hi hd in hs.
have hc : T `\` (E `&` B) `<=` ((T `&` B) `\` E) `|` (T `\` B).
  move=> x [ht hn]; case: (pselect (B x))=> hb.
  - left; split; first by split.
    move=> he; apply: hn; by split.
  - right; by split.
have hh := @measure_binary_cover R X mu hm _ _ _ hc.
rewrite (hB T) hs -addeA.
apply: leeD; [exact: lexx|exact: hh].
Qed.
