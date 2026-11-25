(** Federer (1969), 3.2.5, p. 245: the completed
    measurable-set step for composition with the injective
    Borel pieces. Expand the Borel plus null argument using
    2.2.3 and the countable measurability of the image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSplit MeasureFiniteClosure MeasureAlmostBasic
  TopologicalBorel BorelFamilyBasic BorelFunctionUP BorelFunctionBasic BorelRegularMeasureUP
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableSubsets CountablyMeasurableBorelCore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [completed_borel_relative_preimage]: supporting
    measurability step for condition (1) of Federer 3.2.5,
    p. 245. Borel preimages and null inverse images suffice
    on a piece whose represented image is countably measurable.
    This does not assume a globally sigma-finite target measure. *)
Theorem completed_borel_relative_preimage (R:realType) (X Y:topologicalType)
    (mu:set X->\bar R) (beta:set Y->\bar R)
    (hm:is_measure mu) (hb:is_measure beta) (hr:is_borel_regular_measure beta)
    (f:X->Y) (E:set X):
  (forall B,borel_set B -> measure_measurable mu B) ->
  is_borel_function f -> borel_set E ->
  measure_countably_measurable beta (f @` E) ->
  (forall N,beta N=0 -> mu (E `&` (f @^-1` N))=0) ->
  forall T,measure_measurable beta T -> measure_measurable mu (E `&` (f @^-1` T)).
Proof.
move=>hMB hf hE hImage hNull T hT.
have hImageMeas:=countably_measurable_set_measurable hb hImage.
have hRelMeas:measure_measurable beta (T `&` (f @` E)):=
  measure_measurable_intersection hb hT hImageMeas.
have hRelCount:=@measurable_subset_countably_measurable R Y beta hb
  (T `&` (f @` E)) (f @` E) hRelMeas (fun y h=>h.2) hImage.
have [D [hD [hDA hND]]]:=countably_measurable_borel_core hb hr hRelCount.
pose N:=(T `&` (f @` E)) `\` D.
have hPreD:measure_measurable mu (E `&` (f @^-1` D)).
  apply:hMB; exact (borel_family_binary_intersection (borel_sets_family X) hE
    (borel_function_preimage hf hD)).
have hPreN:mu (E `&` (f @^-1` N))=0:=hNull N hND.
have hEq:E `&` (f @^-1` T)=
    (E `&` (f @^-1` D)) `|` (E `&` (f @^-1` N)).
  apply/seteqP; split=>x.
  - move=>[hx hTx]; case:(pselect (D (f x)))=>hDx.
    + left; by split.
    + right; split=>//; split=>//; split=>//; by exists x.
  - move=>[[hx hDx]|[hx [[hTx _] _]]]; last by split.
    split=>//; exact (hDA (f x) hDx).1.
rewrite hEq; exact (measure_measurable_union hm hPreD (measure_null_measurable hm hPreN)).
Qed.
