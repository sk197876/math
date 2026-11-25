(** Federer (1969), 2.4.16, p. 89: real measurable inputs and tests belong
    to the scalar measurable normed-function space A once measurability is
    known. The essential-separability condition is automatic because the
    real vector space is spanned by one. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP
  MeasureUP MeasureBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  ClosedLinearSpanUP ClosedLinearSpanSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_real_function_in_normed_space]: supporting
    scalar A membership in Federer 2.4.16, p. 89. This holds for
    every measurable partial function, without finite norm or countable
    measurability of its nonzero locus. *)
Lemma measurable_real_function_in_normed_space (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measurable_normed_function mu f.
Proof.
move=> hf; split=> //.
pose S : set (real_norm_metric_space (scalar_absolute_value_norm R)) := [set 1%R].
pose Z := @ClosedLinearSpan.value R R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) S.
have hZ := @ClosedLinearSpan.laws R R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) S.
have h1 : Z 1%R by apply: (closed_linear_span_contains hZ).
have hall (y : R) : Z y.
  have hy := subspace_scale y h1; by rewrite /GRing.scale /= mulr1 in hy.
exists Z; split; first exact: ClosedLinearSpan.countable_separable (countable1 _).
have he : partial_function_preimage f [set y | ~ Z y] = set0.
  apply/seteqP; split; last by move=> x [].
  by move=> x [y [_ hy]]; exact: hy (hall y).
rewrite he; exact: measure_empty.
Qed.
