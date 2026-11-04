(** Federer (1969), 3.2.46, p. 282: replace a
    local coordinate representative only on its actual open
    patch. This supporting measurability consequence of
    2.3.2, p. 73, retains both partial graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  RestrictedFunctionMeasurability MeasurableAlmostModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [restricted_graph_agreement_measurable]:
    equality of actual graphs on V transfers measurability
    for the measure restricted to V, supporting 3.2.46,
    p. 282. V and the original total mass need
    not be finite; outside values are never compared. *)
Theorem restricted_graph_agreement_measurable (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (V : set X)
    (F G : partial_function X Y) :
  is_measure mu -> is_measure_measurable_function mu F ->
  (forall x, V x -> forall y, partial_function_graph F x y <-> partial_function_graph G x y) ->
  is_measure_measurable_function (measure_restrict mu V) G.
Proof.
move=> hMu hF hAgreement.
pose nu := measure_restrict mu V.
have hNu := measure_restrict_is_measure hMu V.
have hFLocal := @measurable_function_for_restricted_measure R X Y mu hMu V F hF.
have hV : measure_almost_everywhere nu V.
  rewrite /measure_almost_everywhere /nu /measure_restrict.
  have hEmpty : V `&` (~`V)=set0 by apply/seteqP; split=> [x [hx hn]|x []]; exact: hn hx.
  rewrite hEmpty; exact: measure_empty.
apply: (@measurable_function_almost_equal R X Y nu hNu F G hFLocal).
apply: (@measure_almost_everywhere_mono R X nu hNu _ _ _
  (@measure_almost_everywhere_and R X nu hNu _ _ hV (measurable_function_domain hFLocal))).
move=> x [hx [y hy]]; exists y; split; first exact hy.
exact: (hAgreement x hx y).1 hy.
Qed.
