(** Federer (1969), 3.2.46, p. 282: the area
    extension is summed over the original injective-differential
    Borel pieces of 3.2.2, p. 242. Actual image masses,
    genuine varying target Jacobians and actual counting
    multiplicities are retained in this supporting Borel case. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormMetricScaleContinuity NormClassZeroWhole
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  RiemannianTensorUP RiemannianMetricCarrier RiemannianChartLift RiemannianHausdorff
  RiemannianTargetJacobian RiemannianPieceAreaDensity
  LipschitzUP InjectiveDifferentialPieceUP InjectiveDifferentialCover InnerOwnNormTopology
  TopologicalBorel BorelRegularMeasureUP BorelPartition BorelSubordinatePartition
  InjectiveBorelImage MeasureUP MeasureRestriction MeasureImagePullback MeasureDensity
  AreaInjectiveBorel PartitionMultiplicityIntegral MappingMultiplicity
  MeasureIntegralUP ExtendedRealOrderTopology PartialFunctionBasic
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_area_injective_borel]: sum the
    actual Riemannian image costs of the univalent Borel
    partition, supporting 3.2.46, p. 282, by the
    partition argument of 3.2.3, p. 243. Duplicate
    image points keep their original source multiplicity;
    infinite masses and degree zero are included. *)
Theorem riemannian_area_injective_borel (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hf : forall x, A (f x)) (hp : 0<=m%:R :> R) (S : set (R_n R m)) :
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] S ->
  S `<=` injective_differential_locus f ->
  is_measure_integral (riemannian_hausdorff_measure hh m%:R hp)
    (partial_function_total (fun y=>(@mapping_multiplicity R _ _
      (@riemannian_chart_lift R _ n A h hh f hf) S y : extended_real_line R)))
    (measure_with_density (@euclidean_lebesgue_measure R m)
      (@extended_target_riemannian_jacobian R m n A h hh f hf m) S).
Proof.
move=> hLip hS hLocus.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose M := [the metricType R of riemannian_metric_space hh].
pose F := @riemannian_chart_lift R X n A h hh f hf.
pose phi := @euclidean_lebesgue_measure R m.
pose J := @extended_target_riemannian_jacobian R m n A h hh f hf m.
pose nu := measure_with_density phi J.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hPhi := euclidean_lebesgue_is_measure R m.
have hJPositive := @target_riemannian_jacobian_nonnegative_almost R m n A h hh f hf m hLip.
have hNu := measure_with_density_is_measure hPhi hJPositive.
have hBeta := @riemannian_hausdorff_is_measure R n A h hh m%:R hp.
have hCont : continuous f.
  have [L [hL hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hContNorm : continuous (fun x : real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))=>
    (f x : real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))).
  have [L [hL hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R _ _ f L (ltW hL)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hZero := @norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f hContNorm.
have [G hG] := injective_differential_borel_cover_exists hZero (ltr1n R 2).
have hGB B : G B -> @borel_set X B.
  move=> hB; exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) B).2 (hG.2.2 B hB).1).
have hCover : S `<=` \bigcup_(B in G) B by rewrite hG.2.1.
have [H [hH hSub]] := borel_countable_cover_subordinate_partition hS hG.1 hGB hCover.
have hBorel B (hB : H B) : @borel_set X B := borel_partition_members hH hB.
have hMeasNu B (hB : H B) : measure_measurable nu B.
  apply: (@measure_with_density_measurable R X phi hPhi J B hJPositive).
  exact (@borel_regular_borel_measurable R X phi hPhi (euclidean_lebesgue_borel_regular R m)
    B (hBorel B hB)).
have hInj B (hB : H B) : {in B &, injective f}.
  have [_ [C [hC hBC]]] := hSub B hB.
  move=> x y hx hy hEq.
  exact ((hG.2.2 C hC).2.2.1 x y (mem_set (hBC x (set_mem hx)))
    (mem_set (hBC y (set_mem hy))) hEq).
have hFInj B (hB : H B) : {in B &, injective F}.
  move=> x y hx hy hEq.
  exact (hInj B hB x y hx hy (congr1 (fun z : M=>val z) hEq)).
have hImages B (hB : H B) : measure_measurable beta (F @` B).
  have hFCont := @riemannian_chart_lift_continuous R X n A h hh f hf hCont.
  have hImage : @borel_set M (F @` B).
    apply: (@injective_borel_image_borel R X M F B (@euclidean_metric_complete R m)
      (@euclidean_metric_separable R m) (@metric_hausdorff R M) hFCont (hBorel B hB)).
    move=> x y hx hy hEq; exact: hFInj B hB x y (mem_set hx) (mem_set hy) hEq.
  exact (@borel_regular_borel_measurable R M beta hBeta
    (@riemannian_hausdorff_borel_regular R n A h hh m%:R hp) (F @` B) hImage).
have hPiece B (hB : H B) : nu B=beta (F @` B).
  have hEqual := @riemannian_piece_area_density R m n A h hh f hf hp B hLip
    (hBorel B hB) (hInj B hB).
  have hValue := congr1 (fun mu=>mu setT) hEqual.
  rewrite /measure_restrict /measure_image_pullback !setIT in hValue.
  exact: esym hValue.
have hSum : nu S=nonnegative_sum H (fun B=>beta (F @` B)).
  have hPartitionSum : nu S=nonnegative_sum H (fun B=>nu B) :=
    @measure_borel_partition_sum R X nu hNu S H hH hMeasNu.
  rewrite hPartitionSum.
  apply: nonnegative_sum_ext=> B hB; exact: hPiece B hB.
have hIntegral := @partition_univalent_multiplicity_integral R X M F S H beta hBeta
  hH hFInj hImages.
rewrite -hSum in hIntegral; exact hIntegral.
Qed.
