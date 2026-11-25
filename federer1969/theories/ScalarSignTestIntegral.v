(** Federer (1969), 2.4.16, p. 89: u=sign(f) attains phi_1(f). The same
    identity also covers zero and infinite norms under the erratum's
    unit-ball convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct PartialNormPower
  RealPower MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm
  ScalarSignTest MeasureLoneNormIntegralGeneral MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_sign_test_integral]: the p=1 attaining
    integral in Federer 2.4.16, p. 89. The input norm need not be finite. *)
Lemma scalar_sign_test_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  is_measure_integral mu (partial_scalar_product f (partial_scalar_sign f))
    (measure_lp_norm mu (fun y : R => `|y|%R) 1%R f).
Proof.
move=> hf; have hi := @measurable_lone_norm_integral R X R^o _ (scalar_absolute_value_norm R) mu hm f hf.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
rewrite partial_scalar_product_graph; split.
- move=> [y [hy he]]; exists y,(Num.sg y); split=> //; split; first by exists y; split.
  rewrite (@real_power_one_exponent R `|y| (normr_ge0 y)) in he.
  by rewrite mulrC -normrEsg.
- move=> [y [v [hy [[w [hw hwv]] hyv]]]].
  have hwy : w=y := partial_function_single_valued hw hy.
  rewrite hwy in hwv; exists y; split=> //.
  by rewrite -hwv mulrC -normrEsg in hyv; rewrite (@real_power_one_exponent R `|y| (normr_ge0 y)).
Qed.

(** Source for [scalar_sign_test_sign_matching]: the endpoint
    test has the required sign in Federer 2.4.16, p. 89; sign is idempotent. *)
Lemma scalar_sign_test_sign_matching (R : realType) (X : Type)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_sign_matching_test f (partial_scalar_sign f).
Proof.
move=> x z; split.
- move=> [y [hy he]]; exists (Num.sg y); split; first by exists y; split.
  by rewrite sgr_id.
- move=> [v [[y [hy hyv]] hvz]]; exists y; split=> //.
  by rewrite -hyv sgr_id in hvz.
Qed.
