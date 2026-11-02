(** Federer (1969), 2.4.16, pp. 89–90: total-function version of the
    attaining power test, used for the approximants in the infinite-norm
    argument. Source context and exact formula: DualPowerTest.v and
    DualPowerTestAdmissible.v. This adapter changes only the graph
    representation; it preserves all values and domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialScalarProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm MeasureLpAlmostEquality MeasureLpNormAlmostEquality
  MeasureDualTestUP DualPowerTest MeasurableDualPowerTest DualPowerTestAdmissible ConjugateExponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_dual_power_test_admissible]: the total
    norming function in Federer 2.4.16, p. 89, evaluated on a
    total measurable input of positive finite norm. *)
Lemma total_dual_power_test_admissible (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 < p)%R -> (0 < a)%R -> is_measure_measurable_function mu (partial_function_total f) ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)=a%:E ->
  let u := fun x => (dual_power_test p a (f x) : real_norm_metric_space (scalar_absolute_value_norm R)) in
  is_finite_lp_unit_test mu (finite_conjugate_exponent p) (partial_function_total u) /\
  is_measure_integral mu (partial_scalar_product (partial_function_total f) (partial_function_total u)) a%:E.
Proof.
move=> hp ha hf hfa u.
have [hu [_ hi]] := @dual_power_test_admissible R X mu hm p a _ hp ha hf hfa.
have he : measure_almost_equal mu (partial_dual_power_test p a (partial_function_total f)) (partial_function_total u).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (u x); split=> //; exists (f x); by split.
have hul := @measure_lp_function_almost_equal R X R^o _ (scalar_absolute_value_norm R) mu hm _ _ _ hu.1 he.
have hnorm := @measure_lp_norm_almost_equal R X R^o _ (scalar_absolute_value_norm R) mu hm _ _ _
  hu.1.1 hu.1.2.1.1 hul.2.1.1 he.
split.
- split; first exact hul.
  by rewrite -hnorm; exact hu.2.
-
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
rewrite !partial_scalar_product_graph; split.
- move=> [v [w [hv [[y [hy hyw]] hvw]]]].
  exists v,w; split=> //; split=> //.
  by change (u x=w); rewrite -(hy : f x=y) in hyw.
- move=> [v [w [hv [hw hvw]]]].
  exists v,w; split=> //; split=> //; exists (f x); by split.
Qed.
