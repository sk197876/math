(** Federer (1969), 2.4.5, pp. 83–84: supporting outer-measure comparison
    after a null exceptional set is removed. Neither set needs to be
    measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_subset_bound]: supporting null-exception
    comparison in Federer 2.4.5, pp. 83–84 *)
Lemma measure_almost_subset_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  measure_almost_everywhere mu [set x | A x -> B x] -> mu A <= mu B.
Proof.
move=> h; pose E := ~` [set x | A x -> B x].
have hc : A `<=` B `|` E.
  move=> x hx; have [hp|hp] := pselect (A x -> B x).
  - left; exact: hp hx.
  - by right.
have hb := @measure_binary_cover R X mu hm A B E hc.
have he : mu E = 0 := h.
by rewrite he adde0 in hb.
Qed.
