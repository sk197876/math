(** Federer (1969), 3.2.38, p. 275: higher-degree intrinsic
    coefficients vanish on lower-dimensional affine images. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure HausdorffLipschitzImages
  LipschitzUP EuclideanAboveDimensionNull ProjectedVolumeMeasurability IntegralGeometricGauge
  OrthogonalProjectionProbability NonnegativeExtendedProbabilityConstant
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_null_integral_geometric_gauge]: supporting
    vanishing of zeta^j(g(K)) for j>m in Federer 3.2.38, p. 275.
    Every actual orthogonal projection is a contraction; H^j nullity
    gives zero projected Lebesgue volume. The actual probability norm
    of the identically zero projected-volume function vanishes.
    Arbitrary original sets and every exponent at least one remain. *)
Lemma hausdorff_null_integral_geometric_gauge (R:realType) n j (hjn:(j<=n)%N) t
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  (1<=t)%E ->@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) j S=0%E ->
  @integral_geometric_gauge R n j hjn t S=0%E.
Proof.
move=>ht hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R j).
pose P:=orthogonal_projection_metric_space R n j.
have hProjected (p:P):projected_volume_function S p=0%E.
  have hLip:is_metric_lipschitz_bound setT (euclidean_projection_linear p:X->Y) 1.
    split; first exact:ler01.
    move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
  have hBound:=@hausdorff_lipschitz_image_bound R X Y (euclidean_projection_linear p) 1 j hLip S.
  rewrite hNull mule0 in hBound.
  rewrite /projected_volume_function -(@euclidean_hausdorff_spherical_lebesgue R j _).1.
  apply/eqP; rewrite eq_le hBound; exact:measure_nonnegative (@hausdorff_measure_is_measure R _ j) _.
have hFunction:projected_volume_function (m:=j) S=(fun _:P=>(0 : \bar R)).
  apply:funext=>p; exact:hProjected.
rewrite /integral_geometric_gauge hFunction
  (@probability_nonnegative_extended_constant_norm R P _ (@theta_star_is_measure R n j hjn)
    0 t (@theta_star_total R n j hjn) (lexx 0%E) ht) mule0.
reflexivity.
Qed.

(** Source for [above_source_dimension_image_intrinsic_zero]: supporting
    the j>m coefficients in Federer 3.2.38, p. 275. The image
    of any globally Lipschitz map from R^m has zero j-dimensional
    Hausdorff measure for j>m. The proved null-gauge law discharges
    all higher coefficients; no injectivity, compactness or rank
    condition is needed for this supporting conclusion. *)
Lemma above_source_dimension_image_intrinsic_zero (R:realType) m n j (hjn:(j<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (L:R) Q:
  (m<j)%N ->is_metric_lipschitz_bound setT f L ->
  @integral_geometric_gauge R n j hjn 1 (f @` Q)=0%E.
Proof.
move=>hmj hLip; apply:hausdorff_null_integral_geometric_gauge; first exact:lexx.
have hBound:=@hausdorff_lipschitz_image_bound R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n)) f L j hLip Q.
rewrite (@euclidean_hausdorff_above_dimension_zero R m j Q hmj) mule0 in hBound.
apply/eqP; rewrite eq_le hBound; exact:measure_nonnegative (@hausdorff_measure_is_measure R _ j) _.
Qed.
