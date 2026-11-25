(** Federer (1969), 2.4.1, p. 81: the joint fibre measures f(r,s) used in
    the additive proof. Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureBasic
  MeasurableFunctionUP MeasureStepFunctionUP MeasureStepFibres NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_step_joint_fibre]: direct abbreviation
    f(r,s) in Federer 2.4.1, p. 81. *)
Definition measure_step_joint_fibre (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u v : partial_function X (real_line_metric R)) (p : R * R) :=
  mu (partial_function_preimage u [set p.1] `&` partial_function_preimage v [set p.2]).

(** Source for [measure_step_joint_fibre_nonnegative]: positivity
    of the common-refinement measures in Federer 2.4.1, p. 81. *)
Lemma measure_step_joint_fibre_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) p :
  0 <= measure_step_joint_fibre mu u v p.
Proof. exact: measure_nonnegative. Qed.

(** Source for [measure_step_joint_fibre_row]: the row-sum identity used in
    Federer 2.4.1, p. 81 *)
Lemma measure_step_joint_fibre_row (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u -> is_measure_measurable_function mu v ->
  countable (partial_function_range v) -> forall r : R,
    nonnegative_sum setT (fun s : R => measure_step_joint_fibre mu u v (r,s)) =
      mu (partial_function_preimage u [set r]).
Proof.
move=> hu hv hc r; rewrite /measure_step_joint_fibre /=.
exact (@measure_countable_range_fibre_partition R X mu hm v
  (partial_function_preimage u [set r]) hv hc (@measurable_real_fibre R X mu hm u hu r)).
Qed.

(** Source for [measure_step_joint_fibre_column]: the column-sum identity
    used in Federer 2.4.1, p. 81 *)
Lemma measure_step_joint_fibre_column (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u -> is_measure_measurable_function mu v ->
  countable (partial_function_range u) -> forall s : R,
    nonnegative_sum setT (fun r : R => measure_step_joint_fibre mu u v (r,s)) =
      mu (partial_function_preimage v [set s]).
Proof.
move=> hu hv hc s.
rewrite -(@measure_step_joint_fibre_row R X mu hm v u hv hu hc s).
apply: nonnegative_sum_ext=> r _; by rewrite /measure_step_joint_fibre setIC.
Qed.
