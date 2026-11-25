(** Federer (1969), 2.4.1, p. 80: real scalar multiplication of step
    functions. Source context: MeasureStepFunctionUP.v. The narrow scalar
    continuity imports provide only real multiplication continuity, as in
    the existing MeasurableRealArithmetic.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic
  MeasureStepFunctionUP PartialFunctionRangeOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_real_function_scale]: scalar operation
    in Federer 2.4.1, p. 80, with unchanged partial domain. *)
Definition partial_real_function_scale (R : realType) (X : Type) (c : R)
    (u : partial_function X (real_line_metric R)) :=
  partial_function_postcompose u (fun y => (c*y : real_line_metric R)).

(** Source for [measurable_real_function_scale]: supporting
    measurability of scalar multiples in Federer 2.4.1, p. 80. *)
Lemma measurable_real_function_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (u : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u ->
  is_measure_measurable_function mu (partial_real_function_scale c u).
Proof.
move=> hu; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm u _ hu).
apply: continuous_borel_function.
change (continuous (fun y : R^o => c*y)); move=> y; apply: cvgM.
- exact: cvg_cst.
- exact: cvg_id.
Qed.

(** Source for [partial_real_scale_range_countable]: supporting
    countable range after scaling in Federer 2.4.1, p. 80. *)
Lemma partial_real_scale_range_countable (R : realType) (X : Type) (c : R)
    (u : partial_function X (real_line_metric R)) :
  countable (partial_function_range u) ->
  countable (partial_function_range (partial_real_function_scale c u)).
Proof. exact: partial_postcomposition_range_countable. Qed.

(** Source for [partial_real_scale_fibre]: the nonzero-scalar fibre identity
    in Federer 2.4.1, p. 80 *)
Lemma partial_real_scale_fibre (R : realType) (X : Type) (c : R)
    (u : partial_function X (real_line_metric R)) :
  c != 0 -> forall y : R,
  partial_function_preimage (partial_real_function_scale c u) [set c*y] =
    partial_function_preimage u [set y].
Proof.
move=> hc y; apply/seteqP; split=> x.
- move=> [z [[w [hw he]] hz]]; exists w; split=> //.
  apply: (mulfI hc); by rewrite he hz.
- move=> [w [hw hwY]]; exists (c*y); split=> //; exists w; split=> //.
  by rewrite hwY.
Qed.
