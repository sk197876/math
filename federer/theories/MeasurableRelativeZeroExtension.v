(** Federer (1969), 3.2.5, p. 245: composition
    need only be measurable on the positive-Jacobian locus;
    the modified function is zero elsewhere. This expands
    the zero-extension convention of 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureSplit MeasureFiniteClosure
  MeasurableFunctionUP MeasurableZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_relative_zero_extension]: supporting
    zero-extension measurability in Federer 3.2.5, p. 245.
    Only preimages relative to A must be measurable;
    values on the complement need not define a globally
    measurable function before the zero modification. *)
Lemma measurable_relative_zero_extension (R:realType) (X:choiceType) (Y:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (zero:Y) (A:set X) (u:partial_function X Y):
  measure_measurable mu A ->
  measure_almost_everywhere mu (partial_function_domain u) ->
  (forall U,open U -> measure_measurable mu (A `&` partial_function_preimage u U)) ->
  is_measure_measurable_function mu (partial_function_zero_extension zero A u).
Proof.
move=>hA hDom hPre; constructor.
- exact (@zero_extension_conull_domain R X Y mu hm zero A u hDom).
- move=>U hU; rewrite partial_zero_extension_preimage.
  apply:(measure_measurable_union hm (hPre U hU)).
  case:(pselect (U zero))=>hZero.
  + have hEq:[set x|~A x /\ U zero]=~` A.
      apply/seteqP; split=>x; first by move=>[hx _].
      by move=>hx; split.
    rewrite hEq; exact (measure_measurable_complement hA).
  + have hEq:[set x|~A x /\ U zero]=set0.
      apply/seteqP; split=>x; last by case.
      by move=>[_ hx]; exact (hZero hx).
    rewrite hEq; exact (measure_measurable_empty hm).
Qed.
