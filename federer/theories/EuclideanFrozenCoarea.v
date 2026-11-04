(** Federer (1969), 3.2.46, p. 282: the
    ordinary coarea theorem in actual frozen source and
    target linear coordinates. Both determinant factors
    are proved by 2.7.16 and genuine integral transport;
    the whole original set and every fibre are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps EuclideanLinearRealNull EuclideanLebesgueDimensions
  EuclideanLebesgueDeterminant EuclideanLinearMeasureTransport EuclideanLinearSubsetIntegral
  EuclideanFrozenCoareaFibres EuclideanCoareaFormula CoareaJacobianMeasure
  EuclideanTargetJacobianMeasurable HausdorffMeasure MappingMultiplicity LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureRestriction MeasurePushforward MeasureScaleIntegral MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence InjectivePushforwardIntegral
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_frozen_coarea]: actual application
    of 3.2.11, pp. 248–249, in the frozen
    coordinates used by 3.2.46, p. 282. The
    source integrand is the actual partial target-degree
    Jacobian of M F L^{-1}, evaluated at L(x).
    No rank, finite-mass, Borelness or fibre-integrability
    premise is added; zero target dimension and infinite
    integral values are included. *)
Theorem euclidean_frozen_coarea (R : realType) m n
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n})
    (F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (S : set (R_n R m)) :
  (n<m)%N -> cancel L I -> cancel I L -> injective M ->
  is_metric_lipschitz setT F -> measure_measurable (@euclidean_lebesgue_measure R m) S ->
  exists a, is_measure_subset_integral (@euclidean_lebesgue_measure R m) S
      (partial_function_precompose L (extended_euclidean_target_jacobian (fun z=>M (F (I z))))) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R m)) (m-n)
        (L @` mapping_fibre F S y) : extended_real_line R)))
      (`|euclidean_det M|^-1%:E*(`|euclidean_det L|%:E*a))%E.
Proof.
move=> hnm hLI hIL hM hF hS.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose G := fun z : X=>(M (F (I z)) : Y).
pose T := L @` S.
pose dL := `|euclidean_det L|.
pose dM := `|euclidean_det M|.
have hLInj : injective L := can_inj hLI.
have hdL : 0<dL by rewrite /dL normr_gt0; exact:(euclidean_det_injective L).2 hLInj.
have hdM : 0<dM by rewrite /dM normr_gt0; exact:(euclidean_det_injective M).2 hM.
have hdLi : 0<dL^-1 by rewrite invr_gt0.
have hdMi : 0<dM^-1 by rewrite invr_gt0.
have hT := euclidean_linear_image_measurable hLInj hS.
have [KI [hKI hIBound]] := euclidean_positive_linear_metric_bound I.
have [KM [hKM hMBound]] := euclidean_positive_linear_metric_bound M.
have [KF [hKF hFBound]] := hF.
have hK : 0<KM*(KF*KI) by rewrite !mulr_gt0.
have hG : is_metric_lipschitz setT G.
  exists (KM*(KF*KI)); split; first exact hK; split; first exact:ltW hK.
  move=> x y _ _.
  apply:le_trans (hMBound.2 (F (I x)) (F (I y)) Logic.I Logic.I) _.
  apply:le_trans (ler_wpM2l (ltW hKM) (hFBound.2 (I x) (I y) Logic.I Logic.I)) _.
  rewrite -!mulrA.
  apply:ler_wpM2l; first exact:ltW hKM.
  apply:ler_wpM2l; first exact:ltW hKF.
  exact:hIBound.2 x y Logic.I Logic.I.
have [b [hSource hTarget]] := @federer_3_2_11 R m n G T hnm hG hT.
pose a := (dL^-1%:E*b)%E.
have hRestore : (dL%:E*a)%E=b.
  by rewrite /a muleA -EFinM mulfV ?gt_eqF // mul1e.
exists a; split.
- apply:(@euclidean_linear_subset_integral_iff R m L S
    (extended_euclidean_target_jacobian G) a hLInj hS).2.
  by rewrite hRestore.
- pose v := partial_function_total (fun z : Y=>(@hausdorff_measure R X (m-n)
    (mapping_fibre G T z) : extended_real_line R)).
  have hScale := @measure_scale_integral R Y (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) dM^-1 hdMi v b hTarget.
  have hPush : measure_pushforward M (@euclidean_lebesgue_measure R n)=
      measure_scale dM^-1 (@euclidean_lebesgue_measure R n).
    apply:funext=> V; rewrite /measure_pushforward /measure_scale.
    exact (@euclidean_lebesgue_linear_pushforward R n M ((euclidean_det_injective M).2 hM) V).
  rewrite -hPush in hScale.
  have hPre := (@injective_pushforward_integral_iff R Y Y
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) M v hM _).2 hScale.
  rewrite hRestore.
  apply:(measure_integral_graph_equivalent _ hPre)=> y r.
  change (@hausdorff_measure R X (m-n) (mapping_fibre G T (M y))=r <->
    @hausdorff_measure R X (m-n) (L @` mapping_fibre F S y)=r).
  by rewrite /G /T (euclidean_frozen_coarea_fibre_image F S y hLI hM).
Qed.
