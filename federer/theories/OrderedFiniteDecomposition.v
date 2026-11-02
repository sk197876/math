(** Federer (1969), 2.5.10, p. 101: well-ordering a covering family with
    countable proper prefixes gives disjoint measurable finite pieces. This
    separates the countable-prefix argument from CH and from the closed-set
    cardinal bound. it does not state this intermediate lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal wochoice.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure MeasureCountableClosure
  CardinalSuccessorUP OrderedFamilyDisjointification FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ordered_finite_measure_decomposition]: supporting
    construction for Federer 2.5.10, p. 101. Each piece
    is measurable because only countably many predecessors are removed.
    Enlarging any countable original cover by its countable prefixes
    gives a countable cover by the disjoint pieces. *)
Theorem ordered_finite_measure_decomposition (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (r : rel J) (B : J -> set X) :
  well_order r -> (forall j, D j -> countable (well_order_prefix D r j)) ->
  (forall j, D j -> measure_measurable mu (B j) /\ mu (B j) < +oo) ->
  finite_measure_sets_countably_covered mu D B ->
  is_finite_measure_decomposition mu D (ordered_family_piece D r B).
Proof.
move=> hw hprefix hB hc; split.
- move=> j hj; split.
  + apply: (@measure_measurable_difference R X mu hm _ _ (hB j hj).1).
    apply: (@measure_measurable_countable_union R X J mu hm _ B (hprefix j hj)).
    move=> i [hi _]; exact: (hB i hi).1.
  + apply: le_lt_trans _ (hB j hj).2.
    exact (@measure_mono R X mu hm _ _ (@ordered_family_piece_subset X J D r B j)).
- split; first exact: ordered_family_pieces_disjoint hw.
  move=> T hT; have [C [hCD [hC hcover]]] := hc T hT.
  pose F := \bigcup_(i in C) ([set i] `|` well_order_prefix D r i).
  have hFD : F `<=` D.
    move=> j [i hi [he|[hj _]]] //; move: he=> /= ->; exact: hCD i hi.
  have hFC : countable F.
    apply: bigcup_countable hC _=> i hi.
    rewrite -bigcup2E; apply: bigcup_countable (countableP setT) _.
    move=> [|[|n]] _ /=; [exact: countable1|exact: hprefix i (hCD i hi)|exact: countable0].
  exists F; split=> //; split=> //.
  apply: (@measure_null_subset R X mu hm _ _ _ hcover)=> x [hx hn]; split=> //.
  move=> [i hi hxi]; have [j hj hxj] := ordered_family_piece_prefix_cover hw (hCD i hi) hxi.
  apply: hn; exists j=> //; by exists i.
Qed.
