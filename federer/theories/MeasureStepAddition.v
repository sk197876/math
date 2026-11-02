(** Federer (1969), 2.4.1, pp. 80–81: additivity of the assignment to step
    functions when the sum of their assigned values is defined. The proof
    follows the book's common refinement, weighted product sums, pointwise
    addition and grouping by r+s. Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasurableRealArithmetic MeasureStepFunctionUP PartialFunctionRangeOperations
  MeasureStepCommonRefinement MeasureStepSumFibres MeasureStepWeightedRefinement
  ExtendedRealPartial NonnegativeSum NumericalSum NumericalSumValues NumericalSumAdd
  NumericalSumGrouping NumericalSumRealWeight RealWeightMeasureDistributivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_step_integral_add]: direct additive
    identity of Federer 2.4.1, pp. 80–81, including
    infinite assigned values whenever their partial sum is defined. *)
Theorem measure_step_integral_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) a b z :
  is_measure_step_function mu u -> is_measure_step_function mu v ->
  is_measure_step_integral mu u a -> is_measure_step_integral mu v b ->
  extended_add a b = Some z ->
  is_measure_step_integral mu (partial_real_function_add u v) z.
Proof.
move=> hu hv ha hb hz.
pose F := measure_step_joint_fibre mu u v.
pose A := (@setT R) `*` (@setT R).
have hr := @measure_step_weighted_rows R X mu hm u v a
  (step_function_measurable hu) (step_function_measurable hv) (step_function_countable_range hv) ha.
have hc := @measure_step_weighted_columns R X mu hm u v b
  (step_function_measurable hu) (step_function_measurable hv) (step_function_countable_range hu) hb.
have [hdef hsum] := @numerical_sum_add R [the choiceType of (R*R)%type] A
  (fun p => p.1%:E*F p) (fun p => p.2%:E*F p) a b z hr hc hz.
have he : numerical_sum A (fun p => (p.1+p.2)%:E*F p) =
    numerical_sum A (fun p => p.1%:E*F p+p.2%:E*F p).
  apply: numerical_sum_ext=> p hp; apply: real_weight_measure_distributivity.
  - exact: measure_step_joint_fibre_nonnegative.
  - exact: hdef p hp.
have htot : numerical_sum A (fun p => (p.1+p.2)%:E*F p) = Some z by rewrite he.
have hmap p : A p -> (@setT R) (p.1+p.2)%R by [].
have [g [hg hgz]] := @numerical_sum_grouping R [the choiceType of (R*R)%type] R A setT
  (fun p => (p.1+p.2)%R) (fun p => (p.1+p.2)%:E*F p) z hmap htot.
have hval t : g t = t%:E*mu (partial_function_preimage (partial_real_function_add u v) [set t]).
  pose B := [set p : R*R | (p.1+p.2)%R=t].
  have hind : A `&` [set p : R*R | (p.1+p.2)%R == t] = B.
    apply/seteqP; split=> p; first by move=> [_ /eqP ht].
    move=> ht; split; first by split.
    exact/eqP.
  have hi := hg t Logic.I; rewrite hind in hi.
  have heq : numerical_sum B (fun p => (p.1+p.2)%:E*F p) = numerical_sum B (fun p => t%:E*F p).
    apply: numerical_sum_ext=> p hp; by rewrite (hp : (p.1+p.2)%R=t).
  have hpos p : B p -> 0 <= F p by move=> _; exact: measure_step_joint_fibre_nonnegative.
  rewrite heq (numerical_sum_real_weight_nonnegative t hpos) in hi.
  have hB := @measure_step_sum_fibre_grouping R X mu hm u v
    (step_function_measurable hu) (step_function_measurable hv)
    (step_function_countable_range hu) (step_function_countable_range hv) t.
  rewrite hB in hi; by case: hi=> <-.
rewrite /is_measure_step_integral.
have heq : numerical_sum setT g = numerical_sum setT
    (fun t : R => t%:E*mu (partial_function_preimage (partial_real_function_add u v) [set t])).
  apply: numerical_sum_ext=> t _; exact: hval.
by rewrite -heq.
Qed.

(** Source for [measure_step_function_add]: direct closure
    assertion accompanying the additive identity in Federer 2.4.1,
    pp. 80–81. Undefined sums of opposite infinities remain
    excluded by the hypothesis. *)
Theorem measure_step_function_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) a b z :
  is_measure_step_function mu u -> is_measure_step_function mu v ->
  is_measure_step_integral mu u a -> is_measure_step_integral mu v b ->
  extended_add a b = Some z -> is_measure_step_function mu (partial_real_function_add u v).
Proof.
move=> hu hv ha hb hz; constructor.
- exact (@measurable_real_function_add R X mu hm u v (step_function_measurable hu) (step_function_measurable hv)).
- exact (@partial_real_sum_range_countable R X u v (step_function_countable_range hu) (step_function_countable_range hv)).
- exists z; exact (@measure_step_integral_add R X mu hm u v a b z hu hv ha hb hz).
Qed.
