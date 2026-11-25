(** Federer (1969), 2.4.5, pp. 83–84: supporting countable-additivity
    calculation on selected fibres of a step function. Source context:
    MeasureAlmostSubsetBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureCountableAdditivity
  MeasurableFunctionUP MeasureStepFibres NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_selected_step_fibre_union]: supporting equality of
    the sum of fibre measures and the measure of their union in Federer
    2.4.5, pp. 83–84 *)
Lemma measure_selected_step_fibre_union (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) (D : set R) :
  is_measure_measurable_function mu u -> countable D ->
  nonnegative_sum D (fun y => mu (partial_function_preimage u [set y])) =
    mu (\bigcup_(y in D) partial_function_preimage u [set y]).
Proof.
move=> hu hc; symmetry; apply: (@measure_countable_disjoint_additivity R X R mu hm D _ hc).
- move=> y _; exact (@measurable_real_fibre R X mu hm u hu y).
- move=> y z hy hz hne x [a [ha ea]] [b [hb eb]].
  have he := partial_function_single_valued ha hb.
  apply: (negP hne); apply/eqP; by rewrite -ea -eb.
Qed.
