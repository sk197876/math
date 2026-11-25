(** Federer (1969), 3.2.5, p. 245, supporting
    3.2.46, p. 282: completed target measurability
    pulls back on a measurable source piece with proved
    null-preimage control. Only the represented image
    needs a countable finite-measure cover. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSplit MeasureFiniteClosure MeasureAlmostBasic
  TopologicalBorel BorelFunctionUP BorelFunctionBasic BorelRegularMeasureUP
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableSubsets CountablyMeasurableBorelCore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [completed_measurable_relative_preimage]:
    the Borel-plus-null preimage argument in 3.2.5,
    p. 245, with completed source measurability retained
    for the piece itself, supporting 3.2.46, p. 282.
    No blanket completed preimage implication or globally
    sigma-finite target measure is assumed. *)
Theorem completed_measurable_relative_preimage (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (beta : set Y -> \bar R)
    (hMu : is_measure mu) (hBeta : is_measure beta) (hRegular : is_borel_regular_measure beta)
    (f : X -> Y) (E : set X) :
  (forall D, borel_set D -> measure_measurable mu D) ->
  is_borel_function f -> measure_measurable mu E ->
  measure_countably_measurable beta (f @` E) ->
  (forall N, beta N=0 -> mu (E `&` (f @^-1` N))=0) ->
  forall T, measure_measurable beta T -> measure_measurable mu (E `&` (f @^-1` T)).
Proof.
move=> hBorel hF hE hImage hNull T hT.
have hImageMeas := countably_measurable_set_measurable hBeta hImage.
have hRelMeas := measure_measurable_intersection hBeta hT hImageMeas.
have hRelCount := @measurable_subset_countably_measurable R Y beta hBeta
  (T `&` (f @` E)) (f @` E) hRelMeas (fun y hy=>hy.2) hImage.
have [D [hD [hDA hND]]] := countably_measurable_borel_core hBeta hRegular hRelCount.
pose N := (T `&` (f @` E)) `\` D.
have hPreD : measure_measurable mu (E `&` (f @^-1` D)).
  exact (@measure_measurable_intersection R X mu hMu E (f @^-1` D) hE
    (hBorel _ (borel_function_preimage hF hD))).
have hPreN : mu (E `&` (f @^-1` N))=0 := hNull N hND.
have hEqual : E `&` (f @^-1` T)=(E `&` (f @^-1` D)) `|` (E `&` (f @^-1` N)).
  apply/seteqP; split=> x.
  - move=> [hx hTx]; case: (pselect (D (f x)))=> hDx.
    + left; by split.
    + right; split; first exact hx; split; last exact hDx.
      split; first exact hTx; by exists x.
  - move=> [[hx hDx]|[hx [[hTx _] _]]]; last by split.
    split; first exact hx; exact: (hDA (f x) hDx).1.
rewrite hEqual.
exact (@measure_measurable_union R X mu hMu _ _ hPreD (measure_null_measurable hMu hPreN)).
Qed.
