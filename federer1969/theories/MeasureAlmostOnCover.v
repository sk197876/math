(** Federer (1969), 3.2.19, p. 256: combine the almost-everywhere
    conclusions on the compact chart images and the null uncovered
    remainder. This supporting rule does not require disjointness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_on_countable_cover]: passage from almost
    every point of each psi_i(K_i) to almost every point of W in
    Federer 3.2.19, p. 256. The countable union of exceptional
    sets and the uncovered remainder are both null. *)
Lemma measure_almost_on_countable_cover (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (W : set X) (D : set J) (F : J -> set X) (P : set X) :
  is_measure mu -> countable D -> mu (W `\` (\bigcup_(j in D) F j))=0 ->
  (forall j, D j -> measure_almost_everywhere_on mu (F j) P) ->
  measure_almost_everywhere_on mu W P.
Proof.
move=> hm hCount hLoss hLocal.
have hUnion := @measure_null_countable_union R X J mu hm D
  (fun j=>F j `\` P) hCount hLocal.
have hBad := measure_null_union hm hLoss hUnion.
apply: (measure_null_subset hm _ hBad)=> x [hx hn].
case: (pselect ((\bigcup_(j in D) F j) x))=> hIn.
- have [j hj hxj] := hIn; right; exists j=> //; by split.
- left; by split.
Qed.
