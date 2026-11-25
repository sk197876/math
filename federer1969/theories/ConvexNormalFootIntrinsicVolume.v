(** Supporting the sharp comparison in Federer (1969),
    3.2.45, pp. 279–280: a normal foot
    contracts every intrinsic volume. The scalar-row
    bound is averaged using the original projection
    probability and reflection invariance. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CoveringFamilyUP CompactSetDistanceProfile CompactMetricBounded EuclideanAffineImageGeometry ScalarConvexLength
  UnitNormalGeometry EuclideanHyperplaneGeometry BoundedConvexIsometricEmbedding
  EuclideanProjectionMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability ProjectedVolumeMeasurability
  ConvexIntrinsicVolumeIntegrals ConvexNormalFootImageVolume PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  FiniteNonnegativeIntegralComparison TotalNonnegativeExtendedScaleIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_normal_foot_intrinsic_volume]:
    supporting orthogonal-projection contraction for the sharp
    Q_infinity <= Q_1 comparison in Federer
    3.2.45, pp. 279–280. Average the actual
    reflected scalar-row volume bound. The original
    isometric-injection theorem of 3.2.36, p. 273,
    identifies the reflected intrinsic volume; the
    positive finite original beta factor then cancels.
    Compact convex sources may have zero volume
    and lie in a proper affine plane. The
    positive-degree connection leaves degree zero to
    the existing exact zeroth-volume law. *)
Theorem convex_normal_foot_intrinsic_volume (R : realType) n m (hMN : (m.+1<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R_n R n) :
  K !=set0 -> compact K -> is_inner_convex K ->
  euclidean_inner_product u u= 1%R ->
  @integral_geometric_gauge R n m.+1 hMN 1
    ((normal_foot (@euclidean_inner_productP R n) u) @` K) <=
    @integral_geometric_gauge R n m.+1 hMN 1 K.
Proof.
move=> hNonempty hCompact hConvex hUnit.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose hB := @euclidean_inner_productP R n.
pose P : {linear R_n R n -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (normal_foot hB u) _.
pose rho : {linear R_n R n -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _.
have hCompactImage (L : {linear R_n R n -> R_n R n}) : @compact [the topologicalType of X] (L @` K).
  have h := @euclidean_affine_hom_compact_image R n n (hom_of_linear L) (0%R:X) K hCompact.
  have hFunction : (fun x : X => 0+hom_of_linear L x)%R=(L : X -> X).
    apply: funext=> x; by rewrite hom_of_linearE add0r.
  by rewrite hFunction in h.
have hImageNonempty (L : {linear R_n R n -> R_n R n}) : L @` K !=set0.
  have [x hx] := hNonempty; exists (L x); by exists x.
have hImageConvex (L : {linear R_n R n -> R_n R n}) : is_inner_convex (L @` K).
  exact: linear_image_inner_convex hConvex.
pose C : compact_metric_set X := exist _ K (mem_set (conj hCompact hNonempty)).
have hBound : metric_set_bounded K := compact_metric_diameter_finite C.
have hImageBound (L : {linear R_n R n -> R_n R n}) : @metric_set_bounded R [the metricType R of X] (L @` K).
  pose D : compact_metric_set X := exist _ (L @` K)
    (mem_set (conj (hCompactImage L) (hImageNonempty L))).
  exact: (compact_metric_diameter_finite D).
pose b := @projection_beta R n m.+1 hMN 1.
pose z (S : set X) := @integral_geometric_gauge R n m.+1 hMN 1 S.
pose mu := @orthogonal_projection_probability R n m.+1 hMN.
pose f (S : set X) := projected_volume_function (m:=m.+1) S.
have hIntegral (S : set X) : S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
    is_measure_integral mu (partial_function_total (f S)) (b%:E*z S).
  exact: convex_intrinsic_volume_integral.
have hK := hIntegral K hNonempty hConvex hBound.
have hP := hIntegral (P @` K) (hImageNonempty P) (hImageConvex P) (hImageBound P).
have hR := hIntegral (rho @` K) (hImageNonempty rho) (hImageConvex rho) (hImageBound rho).
have hOrthogonal := @normal_reflection_orthogonal R (R_n R n)
  (@euclidean_inner_product R n) hB u hUnit.
have hReflection : z (rho @` K)=z K.
  apply: (@bounded_convex_isometric_embedding_intrinsic_volume R n n m.+1 hMN hMN
    K rho hNonempty hConvex hBound).
  exact: euclidean_orthogonal_distance hOrthogonal.
have hScaled := @total_nonnegative_extended_scale_integral R _ mu
  (@theta_star_is_measure R n m.+1 hMN) (f (P @` K)) _ (2:R)%:E
  (fun p => projected_volume_function_nonnegative (P @` K) p) hP.
have hTwo : (0:extended_real_line R)<=(2:R)%:E by rewrite lee_fin; exact: ler0n.
have hScaledIntegral := hScaled hTwo.
pose v (i : bool) := if i then f K else f (rho @` K).
pose a (i : bool) := if i then b%:E*z K else b%:E*z (rho @` K).
have hCompare := @finite_nonnegative_integral_comparison R _ _ mu
  (@theta_star_is_measure R n m.+1 hMN)
  (fun p => ((2:R)%:E*f (P @` K) p : extended_real_line R)) v a.
have hNonnegative i p : 0<=v i p.
  case: i; exact: projected_volume_function_nonnegative.
have hValues i : is_measure_integral mu (partial_function_total (v i)) (a i).
  by case: i; [exact hK|exact hR].
have hPoint p : ((2:R)%:E*f (P @` K) p : extended_real_line R)<=\sum_i v i p.
  rewrite big_bool /v /= /f /projected_volume_function !image_comp.
  exact: (@convex_normal_foot_image_volume R n m K (euclidean_projection_linear p) u hCompact hConvex).
have h := hCompare hNonnegative hValues hPoint.
have hValue := measure_upper_integral_unique
  (measure_upper_integral_specification mu _) hScaledIntegral.2.1.
rewrite hValue big_bool /a hReflection in h.
have hNormalized : (2:R)%:E*(b%:E*z (P @` K))<=b%:E*z K+b%:E*z K := h.
rewrite -mule2n -mule_natl in hNormalized.
have hPositive : (0<b)%R := @projection_beta_positive R n m.+1 hMN 1 (lexx 1).
have hTwoFinite : (2:R)%:E \is a fin_num by [].
have hTwoPositive : 0<(2:R)%:E by rewrite lte_fin; exact: ltr0n.
have hBetaFinite : b%:E \is a fin_num by [].
have hBetaPositive : 0<b%:E by rewrite lte_fin.
by move: hNormalized; rewrite (lee_pmul2l hTwoFinite hTwoPositive)
  (lee_pmul2l hBetaFinite hBetaPositive).
Qed.
