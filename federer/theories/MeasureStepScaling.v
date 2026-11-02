(** Federer (1969), 2.4.1, p. 80: homogeneity of the step-function
    assignment. The zero scalar is handled separately, retaining zero times
    infinity equal to zero. Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureBasic
  MeasureStepFunctionUP MeasureStepScalarOperation NonnegativeSum NonnegativeSumSupport
  NumericalSum NumericalSumValues NumericalSumProduct NumericalSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_step_integral_nonzero_scale]: direct nonzero
    homogeneity case in Federer 2.4.1, p. 80 *)
Lemma measure_step_integral_nonzero_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : partial_function X (real_line_metric R)) (c : R) a :
  c != 0%R -> is_measure_step_integral mu u a ->
  is_measure_step_integral mu (partial_real_function_scale c u) (c%:E*a).
Proof.
move=> hc ha; rewrite /is_measure_step_integral.
pose G y := y%:E*mu (partial_function_preimage (partial_real_function_scale c u) [set y]).
have hi x y : (@setT R) x -> (@setT R) y -> (c*x=c*y)%R -> x=y.
  move=> _ _ he; exact (mulfI hc he).
have him : (fun y : R => (c*y)%R) @` setT = setT.
  apply/seteqP; split=> // y _; exists (y/c)%R=> //.
  by rewrite mulrCA mulfV // mulr1.
have hri := @numerical_sum_injective_image R R R setT (fun y => (c*y)%R) G hi.
rewrite him in hri; rewrite hri.
have he : numerical_sum setT (fun y => G (c*y)%R) =
    numerical_sum setT (fun y : R => c%:E*(y%:E*mu (partial_function_preimage u [set y]))).
  apply: numerical_sum_ext=> y _.
  by rewrite /G (@partial_real_scale_fibre R X c u hc y) EFinM muleA.
rewrite he (@numerical_sum_scale R R setT _ c hc).
by rewrite (ha : numerical_sum setT _ = Some a).
Qed.

(** Source for [measure_step_integral_zero_scale]: zero-scalar
    boundary of Federer 2.4.1, p. 80, including an
    infinite original assigned value and an infinite source measure. *)
Lemma measure_step_integral_zero_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_step_integral mu (partial_real_function_scale 0%R u) 0.
Proof.
have hz y : y%:E*mu (partial_function_preimage (partial_real_function_scale 0%R u) [set y]) = 0.
  case: (eqVneq y 0%R)=> [->|hy]; first exact: mul0e.
  have he : partial_function_preimage (partial_real_function_scale 0%R u) [set y] = set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [z [[w [hw hwz]] hzy]].
    apply: (negP hy); apply/eqP.
    by move: hwz; rewrite mul0r hzy=> <-.
  by rewrite he (measure_empty hm) mule0.
have he : numerical_sum setT (fun y : R => y%:E*
    mu (partial_function_preimage (partial_real_function_scale 0%R u) [set y])) =
    numerical_sum setT (fun _ : R => 0).
  apply: numerical_sum_ext=> y _; exact: hz.
rewrite /is_measure_step_integral he.
rewrite (numerical_sum_nonnegative (fun y (_ : (@setT R) y) => lexx (0 : \bar R))).
by rewrite (nonnegative_sum_zero (fun y (_ : (@setT R) y) => erefl (0 : \bar R))).
Qed.

(** Source for [measure_step_function_scale]: direct scalar
    closure and homogeneity of Federer 2.4.1, p. 80,
    with the special zero-product convention used in the conclusion. *)
Theorem measure_step_function_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) (c : R) a :
  is_measure_step_function mu u -> is_measure_step_integral mu u a ->
  is_measure_step_function mu (partial_real_function_scale c u) /\
  is_measure_step_integral mu (partial_real_function_scale c u) (c%:E*a).
Proof.
move=> hu ha.
have hs : is_measure_step_integral mu (partial_real_function_scale c u) (c%:E*a).
  case: (eqVneq c 0%R)=> [->|hc].
  - rewrite mul0e; exact: measure_step_integral_zero_scale.
  - exact: measure_step_integral_nonzero_scale hc ha.
split=> //; constructor.
- exact (@measurable_real_function_scale R X mu hm c u (step_function_measurable hu)).
- exact (@partial_real_scale_range_countable R X c u (step_function_countable_range hu)).
- by exists (c%:E*a).
Qed.
