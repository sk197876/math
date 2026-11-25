(** Federer (1969), 2.4.16, pp. 89–90: measurability of the explicit
    finite-p norming test. The proof uses the project's measurable powers,
    sign and product laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition
  PartialNormedArithmetic RealPower RealPowerDivision DualPowerTest NormPowerScalar ScalarSignBorel
  ScalarNormedProduct MeasureUP MeasurableFunctionUP MeasurablePostcomposition
  MeasurableGraphEquivalence NormPowerScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_dual_power_test]: the attaining function
    from Federer 2.4.16, p. 89, on the exact input domain. *)
Definition partial_dual_power_test (R : realType) (X : Type) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_function_postcompose f (fun y =>
    (dual_power_test p a y : real_norm_metric_space (scalar_absolute_value_norm R))).

(** Source for [measurable_dual_power_test]: supporting
    measurability of the attaining test in Federer 2.4.16, p. 89. *)
Lemma measurable_dual_power_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  1 < p -> 0 < a -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_dual_power_test p a f).
Proof.
move=> hp ha hf; have hd : 0 < p-1 by rewrite subr_gt0.
pose P := fun y : R => (real_power `|y| (p-1) : real_norm_metric_space (scalar_absolute_value_norm R)).
pose Q := fun y : R => (Num.sg y : real_norm_metric_space (scalar_absolute_value_norm R)).
have hP := @measurable_scalar_norm_power R X R^o _ (scalar_absolute_value_norm R) mu hm (p-1) f hd hf.
have hQ := @measurable_function_borel_postcomposition R X _ _ mu hm f Q hf (@scalar_norm_sign_borel R).
have hprod := @measurable_scalar_normed_product R X mu hm _ _ hP hQ.
have hPQ : is_measure_measurable_function mu (partial_function_postcompose f (fun y => (P y * Q y : real_norm_metric_space (scalar_absolute_value_norm R)))).
  apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hprod)=> x z.
  exact: scalar_normed_same_domain_product_graph.
pose c := (real_power a (p-1))^-1.
have hc := @measurable_normed_scalar_multiple R X R^o _ (scalar_absolute_value_norm R) mu hm c _ hPQ.
have he y : c * (P y * Q y) = dual_power_test p a y.
  by rewrite /dual_power_test real_power_division ?normr_ge0 // /c /P /Q mulrCA mulrA.
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hc)=> x z; split.
- move=> [v [[y [hy hyv]] hvz]]; exists y; split=> //.
  by rewrite -hvz -hyv; change (dual_power_test p a y = c*(P y*Q y)); rewrite he.
- move=> [y [hy hyz]]; exists (P y*Q y); split; first by exists y; split.
  change (c*(P y*Q y)=z); by rewrite he.
Qed.
