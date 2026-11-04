(** Federer (1969), 3.2.46, p. 281: a straight segment
    provides the local upper distance estimate by integrating
    its actual tensor speed. Only the original interval values
    and their proved derivative are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground
  ExtendedRealOrderTopology LipschitzUP LipschitzBasic NormedAffineCurve
  RiemannianTensorUP RiemannianCurveCost RiemannianAdmissibleIntegral
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel
  MeasureIntegralUP MeasureSubsetIntegral MeasureSubsetConstantIntegral MeasureIntegralComparison
  LebesgueScalarMeasure IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_affine_segment_admissible]: the
    straight segment between x and y is one of the admissible
    curves of Federer 3.2.46, p. 281, whenever its actual
    interval image lies in A. A singleton segment is allowed. *)
Lemma riemannian_affine_segment_admissible (R : realType) n A
    (x y : inner_metric_space (@euclidean_inner_productP R n)) :
  (forall t : R, 0 <= t <= 1 -> A (x+t*:(y-x))) ->
  is_riemannian_admissible_curve A x y (fun t=>x+t*:(y-x)) 0 1.
Proof.
move=> hImage; split; first exact: ler01; split.
- apply: metric_lipschitz_of_bound.
  apply: (@metric_lipschitz_bound_restrict R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT `[0,1]
    (fun t=>x+t*:(y-x)) _ (fun _ _=>Logic.I)).
  exact: euclidean_affine_curve_lipschitz.
- split; first exact: hImage; split.
  + by rewrite scale0r addr0.
  + by rewrite scale1r addrC subrK.
Qed.

(** Source for [riemannian_affine_segment_cost_upper]: the
    integral of the segment speed is at most its uniform bound,
    giving the upper curve estimate in Federer 3.2.46, p. 281.
    The parameter interval has actual scalar length one; zero
    speed and dimension zero are included. *)
Lemma riemannian_affine_segment_cost_upper (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (x y : inner_metric_space (@euclidean_inner_productP R n)) k :
  (forall t : R, 0 <= t <= 1 -> A (x+t*:(y-x))) -> 0 <= k ->
  (forall t : R, 0 <= t <= 1 -> riemannian_tensor_speed g (x+t*:(y-x)) (y-x) <= k) ->
  (riemannian_curve_cost g (fun t=>(x+t*:(y-x))%R) 0%R 1%R <= k%:E)%E.
Proof.
move=> hImage hk hBound.
pose C := fun t : real_line_metric R=>x+t*:(y-x).
have hC := riemannian_affine_segment_admissible hImage.
have hi := (riemannian_admissible_curve_finite_integral hg hC).1.
have hK : measure_measurable (@lebesgue_scalar_measure R)
    (`[0,1] : set (real_line_metric R)).
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    (lebesgue_scalar_borel_regular R) `[0,1] (closed_borel_set (@segment_closed_real R 0 1))).
have hConst := @measure_nonnegative_constant_subset_integral R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) `[0,1] k%:E (lebesgue_scalar_is_measure R) hK
  (ltac:(by rewrite lee_fin)).
rewrite lebesgue_scalar_segment ?ler01 // subr0 mule1 in hConst.
apply: (measure_integral_monotone (lebesgue_scalar_is_measure R) hi hConst).
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _
  (measure_almost_everywhere_true (lebesgue_scalar_is_measure R))).
move=> t _.
case: (pselect ((`[0,1] : set (real_line_metric R)) t))=> ht.
- exists (riemannian_tensor_speed g (C t) (y-x))%:E,k%:E; split.
  + apply/partial_function_zero_extension_graph; left; split; first exact ht.
    exists (y-x); split; last reflexivity.
    exact (@affine_normed_curve_derivative R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) x (y-x) t).
  + split.
    * apply/partial_function_zero_extension_graph; left; split; [exact ht | reflexivity].
    * rewrite lee_fin; apply: hBound.
      by move: ht; rewrite /mkset in_itv /=.
- exists 0%:E,0%:E; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split; last exact: lexx.
    apply/partial_function_zero_extension_graph; right; by split.
Qed.
