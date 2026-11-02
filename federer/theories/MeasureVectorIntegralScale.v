(** Federer (1969), 2.4.12, pp. 87–88: scalar homogeneity of the vector
    integral. This is a consequence of the dual specification, retaining
    exact partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureLpScaleMembership
  MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence MeasureConullZeroIntegral
  MeasureVectorIntegralUP PartialFunctionalArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_scale]: direct homogeneity of the
    vector integral in Federer 2.4.12, pp. 87–88 Scalar zero is included. *)
Theorem measure_vector_integral_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (real_norm_metric_space hN)) (y : V) :
  is_measure_vector_integral mu f y ->
  is_measure_vector_integral mu (partial_vector_scale c f) (c *: y)%R.
Proof.
move=> [hf hi]; split.
- exact (@measure_lp_function_scale R X V N hN mu hm 1%R c f hf).
- move=> a ha; have [->|hc] := eqVneq c 0%R.
  + rewrite scale0r linear0; apply: (@measure_almost_zero_integral R X mu hm).
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf.2.1.1)).
    move=> x [z hz]; exists (0%R : V); split; last by rewrite linear0.
    apply/partial_vector_scale_graph; exists z; split=> //; by rewrite scale0r.
  + rewrite linearZ /= EFinM.
    have hs := @measure_integral_nonzero_scale R X mu hm c _ _ hc (hi a ha).
    exact: measure_integral_graph_equivalent (partial_functional_scale_graph f a c) hs.
Qed.
