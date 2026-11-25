(** Federer (1969), 2.4.16, p. 90: existence of a full-sign unit test,
    including functions of infinite norm and null nonzero loci. Source
    context and comparison: PositiveIntegrableWeightUP.v. The theorem uses
    only the sealed weight laws; no series or cover representation is
    exposed to the later duality arguments. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP CountablyMeasurableUP PositiveIntegrableWeightSealed WeightedSignTest MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [full_sign_unit_test_exists]: supporting existence
    for the unchanged sign-constrained supremum in Federer 2.4.16,
    pp. 89–90. The exponent q is any finite number at least one. *)
Theorem full_sign_unit_test_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 <= q)%R ->
  is_countably_measure_measurable_function mu (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  exists u : X -> real_norm_metric_space (scalar_absolute_value_norm R),
    is_finite_lp_unit_test mu q (partial_function_total u) /\
    is_sign_matching_test (partial_function_total f) (partial_function_total u).
Proof.
move=> hq hf.
have hA : measure_countably_measurable mu [set x | f x <> 0].
  have he : partial_function_nonzero_locus (0 : real_norm_metric_space (scalar_absolute_value_norm R))
      (partial_function_total f) = [set x | f x <> 0].
    apply/seteqP; split=> x; first by move=> [y [<- hy]].
    by move=> hx; exists (f x); split.
  rewrite -he; exact: countably_measurable_function_locus hf.
pose w := @PositiveIntegrableWeight.value R X mu hm _ hA.
have hw := @PositiveIntegrableWeight.laws R X mu hm _ hA.
exists (weighted_sign_test f w).
exact: (@weighted_sign_test_admissible R X mu hm q f w hw hq
  (countably_measurable_function_measurable hf)).
Qed.
