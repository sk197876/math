(** Federer (1969), 2.4.17, p. 90: multiplicative interpolation of positive
    finite norms. This assembles the finite and infinite Holder exponent
    cases before applying the logarithm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower
  MeasureUP MeasurableFunctionUP MeasureExponentDomain
  MeasureReciprocalInterpolationFinite MeasureReciprocalInterpolationInfinity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reciprocal_interpolation]: Supporting Federer
    2.4.17, p. 90.Distinct reciprocal coordinates exclude only the trivial
    constant-segment case. *)
Lemma measure_reciprocal_interpolation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v a b A B : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 <= u)%R -> (u <= 1)%R -> (0 <= v)%R -> (v <= 1)%R -> u <> v ->
  (0 < a)%R -> (0 < b)%R -> (a+b= 1)%R -> (0 < A)%R -> (0 < B)%R ->
  is_measure_measurable_function mu f ->
  measure_reciprocal_exponent_norm mu f u=A%:E -> measure_reciprocal_exponent_norm mu f v=B%:E ->
  measure_reciprocal_exponent_norm mu f (a * u+b * v)%R <= (real_power A a * real_power B b)%:E.
Proof.
move=> hu hu1 hv hv1 huv ha hb hab hA0 hB0 hf hA hB.
have [hu0|hu0] := eqVneq u 0%R.
- have hvne : v != 0%R by apply/eqP=> hv0; apply: huv; rewrite hu0 hv0.
  have hvp : (0 < v)%R by rewrite lt_neqAle eq_sym hvne hv.
  have hw : (0 < a * u+b * v)%R by rewrite hu0 mulr0 add0r mulr_gt0.
  rewrite /measure_reciprocal_exponent_norm hu0 eqxx /measure_exponent_norm in hA.
  rewrite /measure_reciprocal_exponent_norm (negbTE hvne) /measure_exponent_norm in hB.
  rewrite /measure_reciprocal_exponent_norm (gt_eqF hw) /measure_exponent_norm hu0 mulr0 add0r.
  exact: (@measure_reciprocal_interpolation_infinity R X R^o _ (scalar_absolute_value_norm R) mu hm v a b A B f hvp hv1 ha hb hab hA0 hf hA hB).
have hup : (0 < u)%R by rewrite lt_neqAle eq_sym hu0 hu.
have [hv0|hv0] := eqVneq v 0%R.
- have hw : (0 < a * u+b * v)%R by rewrite hv0 mulr0 addr0 mulr_gt0.
  rewrite /measure_reciprocal_exponent_norm (negbTE hu0) /measure_exponent_norm in hA.
  rewrite /measure_reciprocal_exponent_norm hv0 eqxx /measure_exponent_norm in hB.
  rewrite /measure_reciprocal_exponent_norm (gt_eqF hw) /measure_exponent_norm hv0 mulr0 addr0 [(real_power A a * real_power B b)%R]mulrC.
  apply: (@measure_reciprocal_interpolation_infinity R X R^o _ (scalar_absolute_value_norm R) mu hm u b a B A f hup hu1 hb ha _ hB0 hf hB hA).
  by rewrite addrC.
have hvp : (0 < v)%R by rewrite lt_neqAle eq_sym hv0 hv.
have hw : (0 < a * u+b * v)%R by rewrite addr_gt0 ?mulr_gt0.
rewrite /measure_reciprocal_exponent_norm (negbTE hu0) /measure_exponent_norm in hA.
rewrite /measure_reciprocal_exponent_norm (negbTE hv0) /measure_exponent_norm in hB.
rewrite /measure_reciprocal_exponent_norm (gt_eqF hw) /measure_exponent_norm.
exact: (@measure_reciprocal_interpolation_finite R X R^o _ (scalar_absolute_value_norm R) mu hm u v a b A B f hup hu1 hvp hv1 ha hb hab hf hA hB).
Qed.
