(** Federer (1969), 2.4.16, p. 89: graph identities for the two displayed
    integral computations for the attaining test. Source context and scalar
    identities: DualPowerTest.v. These supporting equalities preserve exact
    partial domains, including zeros of f, and allow transfer through the
    abstract integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  PartialScalarProduct MeasureUpperIntegralScale RealPower RealPowerDivision
  ConjugateExponents DualPowerTest MeasurableDualPowerTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dual_power_test_norm_graph]: supporting identity
    |u|^q=|f|^p/a^p in Federer 2.4.16, p. 89. *)
Lemma dual_power_test_norm_graph (R : realType) (X : Type) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x z :
  1 < p -> 0 < a ->
  (partial_function_graph (partial_extended_function_scale (real_power a p)^-1
    (partial_norm_power (fun y : R => `|y|) p f)) x z <->
   partial_function_graph (partial_norm_power (fun y : R => `|y|) (finite_conjugate_exponent p)
    (partial_dual_power_test p a f)) x z).
Proof.
move=> hp ha.
have he y : real_power `|dual_power_test p a y| (finite_conjugate_exponent p) =
    (real_power a p)^-1 * real_power `|y| p.
  by rewrite dual_power_test_conjugate_power // real_power_division ?normr_ge0 // mulrC.
split.
- move=> [r [[y [hy hyr]] hrz]].
  exists (dual_power_test p a y); split; first by exists y; split.
  by rewrite he EFinM hyr.
- move=> [v [[y [hy hyv]] hvz]].
  exists (real_power `|y| p)%:E; split; first by exists y; split.
  by rewrite -hyv he EFinM in hvz.
Qed.

(** Source for [dual_power_test_product_graph]: supporting identity
    fu=|f|^p/a^(p-1) in Federer 2.4.16, p. 89. *)
Lemma dual_power_test_product_graph (R : realType) (X : Type) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x z :
  1 < p -> 0 < a ->
  (partial_function_graph (partial_extended_function_scale (real_power a (p-1))^-1
    (partial_norm_power (fun y : R => `|y|) p f)) x z <->
   partial_function_graph (partial_scalar_product f (partial_dual_power_test p a f)) x z).
Proof.
move=> hp ha.
have he y : y * dual_power_test p a y =
    (real_power a (p-1))^-1 * real_power `|y| p.
  by rewrite dual_power_test_product // mulrC.
rewrite partial_scalar_product_graph; split.
- move=> [r [[y [hy hyr]] hrz]].
  exists y,(dual_power_test p a y); split=> //; split; first by exists y; split.
  by rewrite he EFinM hyr.
- move=> [y [v [hy [[w [hw hwv]] hyv]]]].
  have hwy : w = y := partial_function_single_valued hw hy.
  rewrite hwy in hwv; exists (real_power `|y| p)%:E; split; first by exists y; split.
  by rewrite -hwv he EFinM in hyv.
Qed.
