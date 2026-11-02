(** Federer (1969), 2.5.10, pp. 100–101: supporting measurability of the
    density glued from its restrictions to finite-measure pieces. This lemma
    supplies the finite-test step; disjointness is unnecessary here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasureCountableClosure MeasureNullModification
  FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cover_measurable_from_pieces]: supporting gluing
    criterion for Federer 2.5.10, pp. 100–101 Measurability on each piece
    suffices because every finite test is covered up to a null set by
    countably many pieces. No measurability of the test is assumed. *)
Theorem finite_cover_measurable_from_pieces (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (E : set X) :
  finite_measure_sets_countably_covered mu D B ->
  (forall j, D j -> measure_measurable mu (E `&` B j)) ->
  measure_measurable mu E.
Proof.
move=> hc hE; apply/(measure_measurable_finite_test hm)=> T hT.
have [C [hCD [hC hN]]] := hc T hT.
pose V := \bigcup_(j in C) (E `&` B j).
have hV : measure_measurable mu V.
  apply: (@measure_measurable_countable_union R X J mu hm C (fun j => E `&` B j) hC)=> j hj.
  exact: hE j (hCD j hj).
have he x : ~ (T `\` \bigcup_(j in C) B j) x -> T x -> (E x <-> V x).
  move=> hn hx; split.
  - move=> hxE.
    have [j hj hxB] : (\bigcup_(j in C) B j) x.
      apply: contrapT=> h; apply: hn; by split.
    exists j=> //; by split.
  - by move=> [j hj [hxE hxB]].
have hi : mu (T `&` E)=mu (T `&` V).
  apply: (@measure_null_modification_value R X mu hm _ _ _ hN)=> x hn; split.
  - move=> [hx hxE]; split=> //; exact: (proj1 (he x hn hx) hxE).
  - move=> [hx hxV]; split=> //; exact: (proj2 (he x hn hx) hxV).
have hd : mu (T `\` E)=mu (T `\` V).
  apply: (@measure_null_modification_value R X mu hm _ _ _ hN)=> x hn; split.
  - move=> [hx hxE]; split=> // hxV; apply: hxE; exact: (proj2 (he x hn hx) hxV).
  - move=> [hx hxV]; split=> // hxE; apply: hxV; exact: (proj1 (he x hn hx) hxE).
by rewrite hi hd -(hV T).
Qed.
