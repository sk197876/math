(** Weighted intrinsic-volume connection for the section
    comparison in Federer (1969), 3.2.45,
    pp. 279–280. Reuse original projected
    averages, reflection isometry and scalar integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CoveringFamilyUP CompactSetDistanceProfile CompactMetricBounded EuclideanAffineImageGeometry ScalarConvexLength
  UnitNormalGeometry EuclideanHyperplaneGeometry BoundedConvexIsometricEmbedding
  EuclideanProjectionMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability ProjectedVolumeMeasurability
  ConvexIntrinsicVolumeIntegrals ConvexIntrinsicFinitePart ZeroDegreeIntegralGauge
  ConvexWeightedReflectionImageVolume PartialFunctionBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness FiniteNonnegativeIntegralComparison TotalNonnegativeExtendedScaleIntegral
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_weighted_reflection_intrinsic_volume]:
    supporting coordinate-stretch comparison for Federer
    3.2.45, pp. 279–280.
    Average the proved weighted scalar-row volume
    inequality over the original projection probability.
    The unit-normal reflection preserves the original
    intrinsic coefficient by 3.2.36,
    p. 273. Positive beta normalization
    gives the absolute-weight factor. The original
    zeroth coefficient covers degree zero. Compact
    convex bodies may be thin or have
    zero positive-degree volume. The independent relation
    on the supplied linear map is proved
    separately for the actual coordinate stretches. *)
Theorem convex_weighted_reflection_intrinsic_volume (R : realType) n k (hKN : (k<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R_n R n)
    (a b : R) (L : {linear R_n R n -> R_n R n}) :
  K !=set0 -> compact K -> is_inner_convex K ->
  euclidean_inner_product u u= 1%R -> (a+b= 1)%R ->
  (forall x, L x=(a*:x+b*:normal_reflection (@euclidean_inner_productP R n) u x)%R) ->
  @integral_geometric_gauge R n k hKN 1 (L @` K) <=
    (`|a|+`|b|)%R%:E*@integral_geometric_gauge R n k hKN 1 K.
Proof.
move=> hNonempty hCompact hConvex hUnit hSum hL.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hImageNonempty (J : {linear R_n R n -> R_n R n}) : J @` K !=set0.
  have [x hx] := hNonempty; exists (J x); by exists x.
case: k hKN=> [hKN|m hKN].
- rewrite (@zero_degree_integral_geometric_gauge R n hKN (L @` K) (hImageNonempty L))
    (@zero_degree_integral_geometric_gauge R n hKN K hNonempty) mule1 lee_fin.
  have h := lerD (ler_norm a) (ler_norm b); by rewrite hSum in h.
- pose hB := @euclidean_inner_productP R n.
  pose rho : {linear R_n R n -> R_n R n} :=
    GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _.
  have hCompactImage (J : {linear R_n R n -> R_n R n}) :
      @compact [the topologicalType of X] (J @` K).
    have h := @euclidean_affine_hom_compact_image R n n (hom_of_linear J) (0%R:X) K hCompact.
    have hFunction : (fun x : X => 0+hom_of_linear J x)%R=(J : X -> X).
      apply: funext=> x; by rewrite hom_of_linearE add0r.
    by rewrite hFunction in h.
  have hImageConvex (J : {linear R_n R n -> R_n R n}) : is_inner_convex (J @` K).
    exact: linear_image_inner_convex hConvex.
  pose C : compact_metric_set X := exist _ K (mem_set (conj hCompact hNonempty)).
  have hBound : metric_set_bounded K := compact_metric_diameter_finite C.
  have hImageBound (J : {linear R_n R n -> R_n R n}) :
      @metric_set_bounded R [the metricType R of X] (J @` K).
    pose D : compact_metric_set X := exist _ (J @` K)
      (mem_set (conj (hCompactImage J) (hImageNonempty J))).
    exact: compact_metric_diameter_finite D.
  pose beta := @projection_beta R n m.+1 hKN 1.
  pose z (S : set X) := @integral_geometric_gauge R n m.+1 hKN 1 S.
  pose mu := @orthogonal_projection_probability R n m.+1 hKN.
  pose f (S : set X) := projected_volume_function (m:=m.+1) S.
  have hIntegral (S : set X) : S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
      is_measure_integral mu (partial_function_total (f S)) (beta%:E*z S).
    exact: convex_intrinsic_volume_integral.
  have hK := hIntegral K hNonempty hConvex hBound.
  have hImage := hIntegral (L @` K) (hImageNonempty L) (hImageConvex L) (hImageBound L).
  have hR := hIntegral (rho @` K) (hImageNonempty rho) (hImageConvex rho) (hImageBound rho).
  have hOrthogonal := @normal_reflection_orthogonal R (R_n R n)
    (@euclidean_inner_product R n) hB u hUnit.
  have hReflection : z (rho @` K)=z K.
    apply: (@bounded_convex_isometric_embedding_intrinsic_volume R n n m.+1 hKN hKN
      K rho hNonempty hConvex hBound).
    exact: euclidean_orthogonal_distance hOrthogonal.
  pose v (i : bool) := if i then
    (fun p => ((`|a|)%:E*f K p : extended_real_line R)) else
    (fun p => ((`|b|)%:E*f (rho @` K) p : extended_real_line R)).
  pose c (i : bool) := if i then (`|a|)%:E*(beta%:E*z K)
    else (`|b|)%:E*(beta%:E*z (rho @` K)).
  have hValues i : is_measure_integral mu (partial_function_total (v i)) (c i).
    case: i.
    + exact: (@total_nonnegative_extended_scale_integral R _ mu
        (@theta_star_is_measure R n m.+1 hKN) (f K) _ (`|a|)%:E
        (fun p => projected_volume_function_nonnegative K p) hK (lee_tofin (normr_ge0 a))).
    + exact: (@total_nonnegative_extended_scale_integral R _ mu
        (@theta_star_is_measure R n m.+1 hKN) (f (rho @` K)) _ (`|b|)%:E
        (fun p => projected_volume_function_nonnegative (rho @` K) p) hR (lee_tofin (normr_ge0 b))).
  have hNonnegative i p : 0<=v i p.
    case: i; apply: mule_ge0; [exact: lee_tofin (normr_ge0 a)|exact: projected_volume_function_nonnegative
      |exact: lee_tofin (normr_ge0 b)|exact: projected_volume_function_nonnegative].
  have hPoint p : f (L @` K) p<=\sum_i v i p.
    rewrite big_bool /v /= /f /projected_volume_function !image_comp.
    exact: (@convex_weighted_reflection_image_volume R n m K (euclidean_projection_linear p)
      u a b L hCompact hConvex hSum hL).
  have h := @finite_nonnegative_integral_comparison R _ _ mu
    (@theta_star_is_measure R n m.+1 hKN) (f (L @` K)) v c hNonnegative hValues hPoint.
  have hValue := measure_upper_integral_unique (measure_upper_integral_specification mu _) hImage.2.1.
  rewrite hValue big_bool /c hReflection in h.
  have hNormalized : beta%:E*z (L @` K)<=
      (`|a|)%:E*(beta%:E*z K)+(`|b|)%:E*(beta%:E*z K) := h.
  have hKValue := @convex_intrinsic_finite_part_value R n m.+1 hKN K hNonempty hConvex hBound.
  have hTotal : (`|a|)%:E*(beta%:E*z K)+(`|b|)%:E*(beta%:E*z K)=
      beta%:E*((`|a|+`|b|)%R%:E*z K).
    rewrite /z hKValue -!EFinM -EFinD.
    congr (_%:E); ring.
  have hBetaFinite : beta%:E \is a fin_num by [].
  have hBetaPositive : 0<beta%:E.
    rewrite lte_fin; exact: (@projection_beta_positive R n m.+1 hKN 1 (lexx 1)).
  by move: hNormalized; rewrite hTotal (lee_pmul2l hBetaFinite hBetaPositive).
Qed.
