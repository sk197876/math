(** Federer (1969), 2.4.16, p. 89: at p=1 the test is sign(f), whose
    essential norm is at most one. The at-most-one condition follows the
    erratum, p. 2, book p. 89 line 19, and includes null measures and zero
    functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  CountablyMeasurableUP CountablyMeasurableZeroPostcomposition MeasureEssentialNorm
  MeasureEssentialNormComparison MeasureLinfinityUP ScalarSignBorel MeasurableRealNormed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_scalar_sign]: the endpoint test sign(f)
    in Federer 2.4.16, p. 89, with its original partial domain. *)
Definition partial_scalar_sign (R : realType) (X : Type)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_function_postcompose f (fun y =>
    (Num.sg y : real_norm_metric_space (scalar_absolute_value_norm R))).

(** Source for [measurable_scalar_sign]: supporting measurability
    of the endpoint test in Federer 2.4.16, p. 89. *)
Lemma measurable_scalar_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu (partial_scalar_sign f).
Proof.
move=> hf; exact: (@measurable_function_borel_postcomposition R X _ _ mu hm f _ hf
  (@scalar_norm_sign_borel R)).
Qed.

(** Source for [scalar_sign_essential_norm_bound]: the norm bound
    for u=sign(f), Federer 2.4.16, p. 89, with the erratum's
    at-most-one convention; no nonzero-norm premise is needed. *)
Lemma scalar_sign_essential_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  measure_essential_norm mu (fun y : R => `|y|%R) (partial_scalar_sign f) <= 1.
Proof.
move=> hf; apply: (@measure_essential_norm_of_almost_bound R X _ mu hm _ _ 1); first exact: lee01.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
move=> x [y hy]; exists (Num.sg y); split; first by exists y; split.
rewrite lee_fin normr_sg; by case: (y != 0%R); rewrite ?ler01.
Qed.

(** Source for [scalar_sign_linfinity_test]: full admissibility
    of the p=1 endpoint test in Federer 2.4.16, p. 89.
    Countable measurability of f's nonzero locus is retained explicitly. *)
Theorem scalar_sign_linfinity_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) f ->
  is_measure_linfinity_function mu (partial_scalar_sign f) /\
  measure_essential_norm mu (fun y : R => `|y|%R) (partial_scalar_sign f) <= 1.
Proof.
move=> hf; have hmeas := countably_measurable_function_measurable hf.
have hu := @measurable_scalar_sign R X mu hm f hmeas.
have hb := @scalar_sign_essential_norm_bound R X mu hm f hmeas.
split=> //; split; first exact: (@measurable_real_function_in_normed_space R X mu hm _ hu).
split; first exact: le_lt_trans hb (ltry _).
apply: (@countably_measurable_zero_postcomposition R X _ _
  (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
  (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) mu hm f _ _ _ (@scalar_norm_sign_borel R) hf).
- change (closed [set (0%R : real_norm_metric_space (scalar_absolute_value_norm R))]).
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- exact: sgr0.
Qed.
