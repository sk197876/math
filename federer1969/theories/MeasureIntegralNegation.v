(** Federer (1969), 2.4.3(1), p. 81: the lower integral of f is minus the
    upper integral of -f. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureStepScalarOperation MeasureStepScaling
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_negate]: pointwise
    negation in Federer 2.4.3(1), p. 81, with unchanged
    partial domain and with the two infinities interchanged. *)
Definition partial_extended_function_negate (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun z => (-z : extended_real_line R)).

(** Source for [lower_step_value_negated_upper]: supporting lower-to-upper
    correspondence in Federer 2.4.3(1), p. 81 *)
Lemma lower_step_value_negated_upper (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  measure_lower_step_values mu f a ->
  measure_upper_step_values mu (partial_extended_function_negate f) (-a).
Proof.
move=> [u [[hu hlu] ha]].
have [hnu hna] := @measure_step_function_scale R X mu hm u (-1)%R a hu ha.
rewrite mulN1e in hna.
exists (partial_real_function_scale (-1)%R u); split=> //; split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
move=> x [y [z [hy [hz hyz]]]].
exists (-y)%R,(-z); split.
- exists y; split=> //; by rewrite mulN1r.
split.
- exists z; by split.
- by rewrite EFinN leeN2.
Qed.

(** Source for [negated_upper_step_value_lower]: reverse
    correspondence for the order-duality proof of Federer
    2.4.3(1), p. 81. *)
Lemma negated_upper_step_value_lower (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) b :
  measure_upper_step_values mu (partial_extended_function_negate f) b ->
  measure_lower_step_values mu f (-b).
Proof.
move=> [u [[hu hlu] hb]].
have [hnu hnb] := @measure_step_function_scale R X mu hm u (-1)%R b hu hb.
rewrite mulN1e in hnb.
exists (partial_real_function_scale (-1)%R u); split=> //; split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
move=> x [y [z [hy [[w [hw he]] hzy]]]].
exists (-y)%R,w; split.
- exists y; split=> //; by rewrite mulN1r.
split=> //; rewrite EFinN leeNl; by rewrite he.
Qed.

(** Source for [measure_lower_integral_negation]: direct
    Federer 2.4.3(1), p. 81, including empty approximant
    families and infinite integral bounds. *)
Theorem measure_lower_integral_negation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_lower_integral mu f = - measure_upper_integral mu (partial_extended_function_negate f).
Proof.
apply: (@measure_lower_integral_unique R X mu f _ _ (measure_lower_integral_specification mu f)).
split.
- move=> a ha; rewrite leeNr.
  apply: (measure_upper_integral_specification mu (partial_extended_function_negate f)).1.
  exact (@lower_step_value_negated_upper R X mu hm f a ha).
- move=> c hc; rewrite leeNl.
  apply: (measure_upper_integral_specification mu (partial_extended_function_negate f)).2=> b hb.
  have hh := hc (-b) (@negated_upper_step_value_lower R X mu hm f b hb).
  by rewrite leeNl in hh.
Qed.
