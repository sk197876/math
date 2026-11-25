(** Federer (1969), 2.4.1, p. 81: expand each step-function sum over the
    common refinement using weighted iterated summation, 2.1.1(11), p. 53.
    Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP
  MeasurableFunctionUP MeasureStepFunctionUP MeasureStepCommonRefinement
  NumericalSum NumericalSumValues NumericalSumProduct NumericalSumWeightedProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_product_swap]: supporting exchange
    of the product coordinates in Federer 2.4.1, p. 81,
    by the reindexing law of 2.1.1(9), p. 53. *)
Lemma numerical_sum_product_swap (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) :
  numerical_sum (U `*` V) f = numerical_sum (V `*` U) (fun p => f (p.2,p.1)).
Proof.
pose swap (p : J*I) := (p.2,p.1).
have he : swap @` (V `*` U) = U `*` V.
  apply/seteqP; split.
  - move=> [x y] [[a b] [ha hb] heq]; case: heq=> <- <-; by split.
  - move=> [x y] [hx hy]; exists (y,x)=> //; by split.
have hi p q : (V `*` U) p -> (V `*` U) q -> swap p=swap q -> p=q.
  case: p=> a b; case: q=> c d; move=> _ _ /= [-> ->]; by [].
rewrite -he; exact: numerical_sum_injective_image hi.
Qed.

(** Source for [measure_step_weighted_rows]: the first expanded
    weighted sum in Federer 2.4.1, p. 81. *)
Lemma measure_step_weighted_rows (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) a :
  is_measure_measurable_function mu u -> is_measure_measurable_function mu v ->
  countable (partial_function_range v) -> is_measure_step_integral mu u a ->
  numerical_sum (setT `*` setT)
    (fun p : R*R => p.1%:E * measure_step_joint_fibre mu u v p) = Some a.
Proof.
move=> hu hv hc ha.
have hp p : (setT `*` setT) p -> 0 <= measure_step_joint_fibre mu u v p.
  move=> _; exact: measure_step_joint_fibre_nonnegative.
rewrite (@numerical_sum_weighted_product R R R setT setT (measure_step_joint_fibre mu u v) idfun hp).
have he : numerical_sum setT (fun r : R => r%:E *
  NonnegativeSum.nonnegative_sum setT (fun s => measure_step_joint_fibre mu u v (r,s))) =
    numerical_sum setT (fun r : R => r%:E * mu (partial_function_preimage u [set r])).
  apply: numerical_sum_ext=> r _; by rewrite (@measure_step_joint_fibre_row R X mu hm u v hu hv hc r).
by rewrite he.
Qed.

(** Source for [measure_step_weighted_columns]: the second
    expanded weighted sum in Federer 2.4.1, p. 81. *)
Lemma measure_step_weighted_columns (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) b :
  is_measure_measurable_function mu u -> is_measure_measurable_function mu v ->
  countable (partial_function_range u) -> is_measure_step_integral mu v b ->
  numerical_sum (setT `*` setT)
    (fun p : R*R => p.2%:E * measure_step_joint_fibre mu u v p) = Some b.
Proof.
move=> hu hv hc hb; rewrite numerical_sum_product_swap.
have he : numerical_sum (setT `*` setT)
    (fun p : R*R => p.1%:E * measure_step_joint_fibre mu u v (p.2,p.1)) =
  numerical_sum (setT `*` setT)
    (fun p : R*R => p.1%:E * measure_step_joint_fibre mu v u p).
  apply: numerical_sum_ext=> p hp; by rewrite /measure_step_joint_fibre /= setIC.
rewrite he; exact: measure_step_weighted_rows hv hu hc hb.
Qed.
