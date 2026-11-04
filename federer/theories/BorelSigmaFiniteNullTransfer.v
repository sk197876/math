(** Federer (1969), 3.2.46, p. 282: completed
    measurability in the original chart is preserved using
    actual null sets and countably finite measure pieces.
    This expands the 2.2.3, p. 61, Borel-sandwich
    argument without assuming a hull difference null for
    an arbitrary or infinite-mass source set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure MeasureCountableClosure
  BorelRegularMeasureUP MeasureBasic MeasureAlmostBasic BorelNullTransfer TopologicalBorel CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_null_transfer_sigma_finite_measurable]:
    the finite Borel sandwich of 2.2.3, p. 61,
    applies on a countable finite-measure cover, supporting
    3.2.46, p. 282. Only the source measure needs
    Borel regularity; preserving its null sets and measuring
    Borel sets suffice for the target measure. *)
Theorem borel_null_transfer_sigma_finite_measurable (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hMu : is_measure mu) (hNu : is_measure nu)
    (hRegular : is_borel_regular_measure mu) :
  measure_countably_measurable mu setT ->
  (forall D, borel_set D -> measure_measurable nu D) ->
  (forall D, mu D=0 -> nu D=0) -> forall S,
  measure_measurable mu S -> measure_measurable nu S.
Proof.
move=> [C [hCount [hCover hFinite]]] hBorel hNull S hS.
have hPiece D (hD : C D) : measure_measurable nu (S `&` D).
  have hSD := measure_measurable_intersection hMu hS (hFinite D hD).1.
  have hBound : mu (S `&` D)< +oo.
    apply: le_lt_trans (measure_mono hMu _) (hFinite D hD).2.
    by move=> x [_ hx].
  exact (@borel_null_transfer_finite_measurable R X mu nu hMu hNu hRegular
    hBorel hNull (S `&` D) hSD hBound).
have hUnion : S=\bigcup_(D in C) (S `&` D).
  apply/seteqP; split=> x.
  - move=> hx.
    have hAll : (\bigcup_(D in C) D) x by rewrite -hCover.
    have [D hD hxD] := hAll; exists D; first exact hD; by split.
  - by move=> [D hD [hx _]].
rewrite hUnion.
exact (@measure_measurable_countable_union R X [the choiceType of set X]
  nu hNu C (fun D=>S `&` D) hCount hPiece).
Qed.
