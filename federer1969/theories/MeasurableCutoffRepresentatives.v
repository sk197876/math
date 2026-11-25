(** Federer (1969), 3.2.5, p. 245: replace g
    by zero off the represented image and ignore a null
    image deficit. Total representatives are proof witnesses;
    the original zero-cutoff graph remains the specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialFunctionExtensionUP PartialFunctionExtensionSealed MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableAlmostModification MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_cutoff_null_enlargement]: ignore the
    null deficit f(A) minus f(B) in Federer 3.2.5(3),
    p. 245, using the almost-equality convention of 2.3.1. *)
Lemma measurable_cutoff_null_enlargement (R:realType) (X:choiceType) (Y:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (zero:Y) (A C:set X) (g:X->Y):
  A `<=` C -> mu (C `\` A)=0 ->
  is_measure_measurable_function mu (partial_function_zero_extension zero A (partial_function_total g)) ->
  is_measure_measurable_function mu (partial_function_zero_extension zero C (partial_function_total g)).
Proof.
move=>hAC hNull hA; apply:(measurable_function_almost_equal hm hA).
have hOff:measure_almost_everywhere mu (~` (C `\` A)).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hOff)=>x hx.
case:(pselect (A x))=>hAx.
- exists (g x); split; apply/partial_function_zero_extension_graph; left; split=>//; exact (hAC x hAx).
- have hCx:~C x by move=>h; apply:hx; split.
  exists zero; split; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [measurable_cutoff_total_representative]: the
    total zero-off-image representative of g in Federer
    3.2.5, p. 245. The witness is supplied by the
    existing opaque total-extension interface; its pointwise
    values and measurability are proved from the cutoff graph. *)
Lemma measurable_cutoff_total_representative (R:realType) (X:choiceType) (Y:topologicalType)
    (mu:set X->\bar R) (zero:Y) (A:set X) (g:X->Y):
  is_measure_measurable_function mu (partial_function_zero_extension zero A (partial_function_total g)) ->
  exists G,is_measure_measurable_function mu (partial_function_total G) /\
    (forall x,A x -> G x=g x) /\ (forall x,~A x -> G x=zero).
Proof.
move=>hMeas.
pose u:=partial_function_zero_extension zero A (partial_function_total g).
pose G:=@PartialFunctionExtension.value X Y u zero.
have hExt:is_partial_function_total_extension u G:=@PartialFunctionExtension.laws X Y u zero.
have hOn x:A x -> G x=g x.
  move=>hx; apply:(hExt x (g x)); apply/partial_function_zero_extension_graph; left; by split.
have hOff x:~A x -> G x=zero.
  move=>hx; apply:(hExt x zero); apply/partial_function_zero_extension_graph; right; by split.
have hValue x:partial_function_graph u x (G x).
  case:(pselect (A x))=>hx.
  - rewrite (hOn x hx); apply/partial_function_zero_extension_graph; left; by split.
  - rewrite (hOff x hx); apply/partial_function_zero_extension_graph; right; by split.
exists G; split; last by split.
apply:(@measurable_function_graph_equivalent R X Y mu u (partial_function_total G) _ hMeas)=>x z.
split.
- move=>hz; exact (partial_function_single_valued (hValue x) hz).
- move=>hz; change (G x=z) in hz; by rewrite -hz.
Qed.
