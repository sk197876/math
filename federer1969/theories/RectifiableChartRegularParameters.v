(** Federer (1969), 3.2.19, p. 256: almost every point of
    each compact chart image satisfies the source-density and actual
    differential hypotheses of 3.2.17, also for a Lipschitz composite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP HilbertFormCompactness NormDifferentialUP LinearEmbeddingContinuity
  LipschitzUP LipschitzBasic RectifiableCompactChartsUP
  EuclideanLebesgueDimensions EuclideanApproximateContext DensityMeasurableSets
  MeasureDensityPoints MeasureSetDensity CenteredBallRelations PartialFunctionUP
  Rademacher EuclideanRectifiableNullImage HausdorffMeasure
  MeasureUP MeasureBasic MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_regular_parameters]: the invocation of
    2.9.11, 3.1.6 and 2.10.11 in Federer 3.2.19, p. 256.
    The retained source points have injective actual chart differential,
    density-one parameter domain and differentiable composite. Their
    images omit only a Hausdorff-null part of the chart image. *)
Theorem rectifiable_chart_regular_parameters (R : realType) m n k
    (lambda : R) (K : set (R_n R m)) (psi : R_n R m -> R_n R n)
    (F : R_n R n -> R_n R k) :
  0<lambda -> is_uniform_compact_rectifiable_chart lambda K psi ->
  @is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  exists A : set (R_n R m), A `<=` K /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      ((psi @` K) `\` (psi @` A))=0%E /\
    forall a, A a ->
      partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
        (@centered_closed_ball_relation R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E /\
      (exists D : Hom (R_n R m) (R_n R n),
        has_norm_differential (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\ injective D) /\
      norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a.
Proof.
move=> hLam hChart [L [hL hF]].
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
have hm := euclidean_lebesgue_is_measure R m.
have hPsi := rectifiable_chart_global_bound hChart.
have hComp : @is_metric_lipschitz R X Z setT (fun x=>F (psi x)).
  exists (L*lambda); split; first exact: mulr_gt0 hL hLam.
  split; first exact: mulr_ge0 (ltW hL) (ltW hLam).
  move=> x y _ _; apply: le_trans (hF.2 (psi x) (psi y) I I) _.
  rewrite -mulrA; exact: (ler_wpM2l (ltW hL) (hPsi.2 x y I I)).
have hKm : measure_measurable mu K.
  exact: (borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)
    (closed_borel_set (compact_closed (@metric_hausdorff R X) (rectifiable_chart_compact hChart)))).
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose Q := measure_density_complement_zero_points mu V K.
pose B := norm_differentiable_at NX (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)).
pose A := K `&` (Q `&` B).
have hQC := @density_complement_zero_points_conclusions R [the metricType R of X]
  mu V K (euclidean_approximate_context R m).
have hQNull : mu (K `\` Q)=0%E := hQC.2.2.2.1 hKm.
have hBNull : mu (~` B)=0%E := federer_3_1_6 hComp.
have hUnion := measure_null_union hm hQNull hBNull.
have hBad : mu (K `\` A)=0%E.
  apply: (measure_null_subset hm _ hUnion)=> x [hx hn].
  case: (pselect (Q x))=> hq; last by left; split.
  right; move=> hb; apply: hn; by split=> //; split.
have hImageBad := euclidean_lipschitz_null_image (metric_lipschitz_of_bound hPsi) hBad.
have hImageLoss : @hausdorff_measure R Y m ((psi @` K) `\` (psi @` A))=0%E.
  apply: (measure_null_subset (@hausdorff_measure_is_measure R Y m) _ hImageBad).
  move=> y [[x hx <-] hn]; exists x=> //; split=> // ha; apply: hn; by exists x.
exists A; split; first by move=> x hx; exact hx.1.
split; first exact hImageLoss.
move=> a [ha [hQ hB]]; split; first exact hQ.
split; last exact hB.
have [D [hD hBounds]] := @rectifiable_chart_differential_bounds R m n lambda K psi hChart a ha.
exists D; split; first exact hD.
apply: (norm_linear_lower_bound_injective
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
exists lambda^-1; split; first by rewrite invr_gt0.
by move=> v; exact: (hBounds v).1.
Qed.
