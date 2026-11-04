(** Federer (1969), 3.2.46, p. 281: translate the second
    genuine curve parameter before concatenation. The actual
    derivative graph and finite integral are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground
  ExtendedRealOrderTopology LipschitzUP NormedCurveDerivativeUP
  NormedCurveParameterTranslation RiemannianTensorUP RiemannianCurveCost
  RiemannianAdmissibleIntegral ScalarIntervalTranslationIntegral
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureSubsetIntegral MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_curve_parameter_translation_bound]:
    a parameter translation preserves the actual Lipschitz bound,
    supporting concatenation in Federer 3.2.46, p. 281. *)
Lemma metric_curve_parameter_translation_bound (R : realType) (Y : metricType R)
    (C : real_line_metric R -> Y) d L :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT C L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT
    (fun t=>C (t+d)) L.
Proof.
move=> hC; split; first exact: hC.1.
move=> t u _ _; have hh := hC.2 (t+d) (u+d) Logic.I Logic.I.
have he : (t+d)-(u+d)=t-u by ring.
by rewrite !real_line_metric_distanceE he in hh.
Qed.

(** Source for [riemannian_translated_curve_admissible]:
    the translated original curve and interval are admissible
    with the same endpoints, supporting Federer 3.2.46, p. 281. *)
Lemma riemannian_translated_curve_admissible (R : realType) n A x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b d :
  is_riemannian_admissible_curve A x y C a b ->
  is_riemannian_admissible_curve A x y (fun t=>C (t+d)) (a-d) (b-d).
Proof.
move=> [hab [[L [hL hBound]] [hImage [hStart hEnd]]]].
have hInterval t : a-d <= t <= b-d -> a <= t+d <= b.
  by move=> /andP [h1 h2]; apply/andP; split; lra.
split; first by lra.
split.
- exists L; split=> //; split; first exact: hBound.1.
  move=> t u ht hu.
  have ht' : a-d <= t <= b-d by move: ht; rewrite /mkset in_itv /=.
  have hu' : a-d <= u <= b-d by move: hu; rewrite /mkset in_itv /=.
  have htI : (`[a,b] : set (real_line_metric R)) (t+d).
    by rewrite /mkset in_itv /=; exact: hInterval.
  have huI : (`[a,b] : set (real_line_metric R)) (u+d).
    by rewrite /mkset in_itv /=; exact: hInterval.
  have hh := hBound.2 _ _ htI huI.
  have he : (t+d)-(u+d)=t-u by ring.
  by rewrite !real_line_metric_distanceE he in hh.
- split; first by move=> t ht; exact: hImage (hInterval t ht).
  split; by rewrite subrK.
Qed.

(** Source for [riemannian_translated_speed_graph]: the
    actual velocity is unchanged under parameter translation,
    supporting the length identity in Federer 3.2.46, p. 281.
    This exact graph law needs no derivative-existence premise. *)
Lemma riemannian_translated_speed_graph (R : realType) n g
    (C : R -> R_n R n) d t z :
  partial_function_graph (riemannian_curve_speed g (fun s=>C (s+d))) t z <->
  partial_function_graph (riemannian_curve_speed g C) (t+d) z.
Proof.
split.
- move=> [v [hv hValue]]; exists v; split.
  + exact ((@normed_curve_parameter_translation_iff R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) C d t v).1 hv).
  + exact hValue.
- move=> [v [hv hValue]]; exists v; split.
  + exact ((@normed_curve_parameter_translation_iff R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) C d t v).2 hv).
  + exact hValue.
Qed.

(** Source for [riemannian_translated_curve_cost]: translation
    preserves the genuine compact-interval length integral used
    in the triangle argument of Federer 3.2.46, p. 281. *)
Lemma riemannian_translated_curve_cost (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b d :
  is_riemannian_admissible_curve A x y C a b ->
  riemannian_curve_cost g (fun t=>C (t+d)) (a-d) (b-d) = riemannian_curve_cost g C a b.
Proof.
move=> hC.
have hi := (riemannian_admissible_curve_finite_integral hg hC).1.
have hTransport := scalar_interval_translation_integral d hi.
have hOriginal : is_measure_subset_integral (@lebesgue_scalar_measure R) `[a-d,b-d]
    (riemannian_curve_speed g (fun t=>C (t+d))) (riemannian_curve_cost g C a b).
  apply: (measure_integral_graph_equivalent _ hTransport)=> t z.
  pose f := partial_function_precompose (fun t=>t+d) (riemannian_curve_speed g C).
  pose q := riemannian_curve_speed g (fun t=>C (t+d)).
  have hRaw : partial_function_graph f t z <-> partial_function_graph q t z.
    exact: iff_sym (@riemannian_translated_speed_graph R n g C d t z).
  have hF := @partial_function_zero_extension_graph (real_line_metric R)
    (extended_real_line R) 0 `[a-d,b-d] f t z.
  have hQ := @partial_function_zero_extension_graph (real_line_metric R)
    (extended_real_line R) 0 `[a-d,b-d] q t z.
  split; move=> hVal.
  - have [[ht hv]|[hn hz]] := hF.1 hVal.
    + exact (hQ.2 (or_introl (conj ht (hRaw.1 hv)))).
    + exact (hQ.2 (or_intror (conj hn hz))).
  - have [[ht hv]|[hn hz]] := hQ.1 hVal.
    + exact (hF.2 (or_introl (conj ht (hRaw.2 hv)))).
    + exact (hF.2 (or_intror (conj hn hz))).
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hOriginal.2.1.
Qed.
