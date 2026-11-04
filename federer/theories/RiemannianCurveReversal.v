(** Federer (1969), 3.2.46, p. 281: rho is symmetric.
    Reverse the actual admissible curve, prove its actual speed
    graph under the parameter reflection, and transport the
    genuine scalar integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground
  ExtendedRealOrderTopology LipschitzUP NormedCurveDerivativeUP
  NormedCurveParameterReflection RiemannianTensorUP RiemannianCurveCost
  RiemannianAdmissibleIntegral ScalarIntervalIsometryIntegral
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureSubsetIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_tensor_speed_negate]: reversing
    velocity preserves its inner-product norm, supporting symmetry
    in Federer 3.2.46, p. 281. Zero velocity is included. *)
Lemma riemannian_tensor_speed_negate (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) v :
  riemannian_tensor_speed g x (-v) = riemannian_tensor_speed g x v.
Proof. by rewrite !(riemannian_tensor_speed_inner_norm hg hx) inner_normN. Qed.

(** Source for [riemannian_reversed_curve_admissible]: reversal
    is among the original compact-interval Lipschitz curves in
    Federer 3.2.46, p. 281, with its endpoints exchanged. *)
Lemma riemannian_reversed_curve_admissible (R : realType) n A x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  is_riemannian_admissible_curve A y x (fun t=>C (a+b-t)) a b.
Proof.
move=> [hab [[L [hL hBound]] [hImage [hStart hEnd]]]].
have hInterval t : a <= t <= b -> a <= a+b-t <= b.
  by move=> /andP [h1 h2]; apply/andP; split; lra.
split=> //; split.
- exists L; split=> //; split; first exact: hBound.1.
  move=> t u ht hu.
  have ht' : a <= t <= b by move: ht; rewrite /mkset in_itv /=.
  have hu' : a <= u <= b by move: hu; rewrite /mkset in_itv /=.
  have htI : (`[a,b] : set (real_line_metric R)) (a+b-t).
    by rewrite /mkset in_itv /=; exact: hInterval.
  have huI : (`[a,b] : set (real_line_metric R)) (a+b-u).
    by rewrite /mkset in_itv /=; exact: hInterval.
  have hh := hBound.2 _ _ htI huI.
  have hDiff : (a+b-t)-(a+b-u) = -(t-u) by ring.
  by rewrite !real_line_metric_distanceE hDiff normrN in hh.
- split; first by move=> t ht; exact: hImage (hInterval t ht).
  split; [have h : a+b-a=b by ring | have h : a+b-b=a by ring]; by rewrite h.
Qed.

(** Source for [riemannian_reversed_speed_graph]: reversal
    preserves exactly the actual speed graph under t |-> c-t,
    supporting the integral comparison in Federer 3.2.46, p. 281.
    No value is assigned where a derivative does not exist. *)
Lemma riemannian_reversed_speed_graph (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (C : R -> R_n R n) c t z :
  A (C (c-t)) ->
  (partial_function_graph (riemannian_curve_speed g (fun s=>C (c-s))) t z <->
   partial_function_graph (riemannian_curve_speed g C) (c-t) z).
Proof.
move=> hx; split; move=> [v [hv hValue]].
- exists (-v); split.
  + exact: (@normed_curve_reflection_derivative_iff R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) C c t v).1 hv.
  + by rewrite (riemannian_tensor_speed_negate hg hx).
- exists (-v); split.
  + exact: (@normed_curve_parameter_reflection R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) C c t v hv).
  + by rewrite (riemannian_tensor_speed_negate hg hx).
Qed.

(** Source for [riemannian_reversed_curve_cost]: the genuine
    length integral is unchanged by reversal, proving the curve
    argument for symmetry in Federer 3.2.46, p. 281. The
    original curve need only be Lipschitz on its own interval. *)
Theorem riemannian_reversed_curve_cost (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  riemannian_curve_cost g (fun t=>C (a+b-t)) a b = riemannian_curve_cost g C a b.
Proof.
move=> hC.
have hi := (riemannian_admissible_curve_finite_integral hg hC).1.
have hTransport := scalar_interval_reflection_integral hi.
have hOriginal : is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (riemannian_curve_speed g (fun t=>C (a+b-t))) (riemannian_curve_cost g C a b).
  apply: (measure_integral_graph_equivalent _ hTransport)=> t z.
  pose f := partial_function_precompose (fun t=>a+b-t) (riemannian_curve_speed g C).
  pose q := riemannian_curve_speed g (fun t=>C (a+b-t)).
  have hGraph : (`[a,b] : set (real_line_metric R)) t ->
      (partial_function_graph f t z <-> partial_function_graph q t z).
    move=> ht.
    have ht' : a <= t <= b by move: ht; rewrite /mkset in_itv /=.
    have hPoint : A (C (a+b-t)).
      apply: hC.2.2.1; have /andP [h1 h2] := ht'; apply/andP; split; lra.
    exact: iff_sym (@riemannian_reversed_speed_graph R n A g hg C (a+b) t z hPoint).
  have hF := @partial_function_zero_extension_graph (real_line_metric R)
    (extended_real_line R) 0 `[a,b] f t z.
  have hQ := @partial_function_zero_extension_graph (real_line_metric R)
    (extended_real_line R) 0 `[a,b] q t z.
  split; move=> hVal.
  - have [[ht hv]|[hn hz]] := hF.1 hVal.
    + exact (hQ.2 (or_introl (conj ht ((hGraph ht).1 hv)))).
    + exact (hQ.2 (or_intror (conj hn hz))).
  - have [[ht hv]|[hn hz]] := hQ.1 hVal.
    + exact (hF.2 (or_introl (conj ht ((hGraph ht).2 hv)))).
    + exact (hF.2 (or_intror (conj hn hz))).
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hOriginal.2.1.
Qed.
