(** Federer (1969), 2.4.3(5), p. 82: positive real homogeneity of the upper
    integral. We transform upper step functions by c and by its inverse,
    then use the abstract infimum laws. Source context:
    PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureStepScalarOperation MeasureStepScaling
  MeasureIntegralUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_scale]: scalar operation
    used in Federer 2.4.3(5), p. 82, with the
    zero-product convention of 2.4.2, p. 81. The theorem
    below requires a strictly positive real scalar. *)
Definition partial_extended_function_scale (R : realType) (X : Type) (c : R)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun z => (c%:E*z : extended_real_line R)).

(** Source for [positive_scaled_upper_step_value]: forward
    upper-function correspondence for Federer 2.4.3(5), p. 82. *)
Lemma positive_scaled_upper_step_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) a :
  (0 < c)%R -> measure_upper_step_values mu f a ->
  measure_upper_step_values mu (partial_extended_function_scale c f) (c%:E*a).
Proof.
move=> hc [u [[hu hlu] ha]].
have [hcu hca] := @measure_step_function_scale R X mu hm u c a hu ha.
exists (partial_real_function_scale c u); split=> //; split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
move=> x [y [z [hy [hz hzy]]]].
exists (c*y)%R,(c%:E*z); split; first by exists y; split.
split; first by exists z; split.
rewrite EFinM lee_pmul2l //; by rewrite lte_fin.
Qed.

(** Source for [inverse_scaled_upper_step_value]: reverse
    upper-function correspondence for Federer 2.4.3(5), p. 82. *)
Lemma inverse_scaled_upper_step_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) b :
  (0 < c)%R -> measure_upper_step_values mu (partial_extended_function_scale c f) b ->
  measure_upper_step_values mu f (c^-1%:E*b).
Proof.
move=> hc [u [[hu hlu] hb]].
have [hiu hib] := @measure_step_function_scale R X mu hm u c^-1 b hu hb.
exists (partial_real_function_scale c^-1 u); split=> //; split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
move=> x [y [z [hy [[w [hw he]] hzy]]]].
exists (c^-1*y)%R,w; split; first by exists y; split.
split=> //; rewrite EFinM lee_pdivlMl //; by rewrite he.
Qed.

(** Source for [measure_upper_integral_positive_scale]: direct
    Federer 2.4.3(5), p. 82, including both infinite
    integral values and empty upper-approximant families. *)
Theorem measure_upper_integral_positive_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) :
  (0 < c)%R -> measure_upper_integral mu (partial_extended_function_scale c f) =
    c%:E * measure_upper_integral mu f.
Proof.
move=> hc; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -lee_pdivrMl //.
  apply: (measure_upper_integral_specification mu f).2=> a ha.
  rewrite lee_pdivrMl //.
  apply: (measure_upper_integral_specification mu (partial_extended_function_scale c f)).1.
  exact (@positive_scaled_upper_step_value R X mu hm c f a hc ha).
- apply: (measure_upper_integral_specification mu (partial_extended_function_scale c f)).2=> b hb.
  rewrite -lee_pdivlMl //.
  apply: (measure_upper_integral_specification mu f).1.
  exact (@inverse_scaled_upper_step_value R X mu hm c f b hc hb).
Qed.
