(** Federer (1969), 2.5.10, pp. 100–101: extending the finite-test covering
    condition to a summable function's support. Countable measurability is
    defined in 2.3.4, p. 76, and retained in L1 by 2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableSequences
  FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cover_covers_countably_measurable_set]: supporting
    countable-support reduction in Federer 2.5.10, pp. 100–101 No
    disjointness of the covering family is needed for this step. *)
Lemma finite_cover_covers_countably_measurable_set (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X) (S : set X) :
  finite_measure_sets_countably_covered mu D B -> measure_countably_measurable mu S ->
  exists C : set J, C `<=` D /\ countable C /\ mu (S `\` \bigcup_(j in C) B j)=0.
Proof.
move=> hc hS.
have [T [he hT]] := (proj1 (countably_measurable_sequence_iff hm S)) hS.
have hp n := hc (T n) (hT n).2.
pose C n := projT1 (cid (hp n)).
have hC n := projT2 (cid (hp n)).
exists (\bigcup_n C n); split.
- move=> j [n _ hj]; exact: (hC n).1 j hj.
- split.
  + apply: bigcup_countable (countableP setT) _=> n _; exact: (hC n).2.1.
  + have hz := @measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm setT
      (fun n => T n `\` \bigcup_(j in C n) B j) (countableP setT) (fun n _ => (hC n).2.2).
    apply: (@measure_null_subset R X mu hm _ _ _ hz)=> x [hx hn].
    rewrite he in hx; have [n _ hxn] := hx; exists n=> //; split=> //.
    move=> [j hj hxj]; apply: hn; exists j=> //; by exists n.
Qed.
