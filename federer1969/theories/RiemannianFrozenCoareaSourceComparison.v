(** Federer (1969), 3.2.46, p. 282: local
    frozen Jacobian and source-density estimates bound the
    actual coarea source integral. These estimates are
    proved separately from tensor continuity. This supporting
    step keeps actual partial derivatives and every original
    source point; no coarea equality is a premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormDifferentialUP NormDifferential EuclideanHomOperator
  EuclideanWholeDifferentialMeasurable EuclideanTargetJacobianMeasurable
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianReferenceFunction
  RiemannianMapDifferential RiemannianMapDifferentialLocal RiemannianMapJacobian
  RiemannianLinearJacobian RiemannianJacobianDensityMeasure
  RiemannianCoareaReferenceSubsetIntegral RiemannianFrozenJacobianCoordinates
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant EuclideanLinearMaps
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialDensityProduct
  LipschitzUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureSubsetIntegral MeasureSubsetIntegralScale MeasureSubsetGraphComparison
  MeasureUpperIntegralScale ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_frozen_coarea_source_bounds]:
    actual source integral comparison in the local-isometry
    reduction of 3.2.46, p. 282. Pointwise
    Jacobian distortion K and source-density distortion s
    give the factor K*s; both directions retain singular
    maps, zero Jacobians and infinite integral values.
    The geometric application must prove these local
    metric estimates, the coordinate agreement and the
    genuine frozen integral separately. *)
Theorem riemannian_frozen_coarea_source_bounds (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) a (ha : A a) b (hb : B b)
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n})
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (S : set (riemannian_metric_space hg)) (K s : R) t :
  is_riemannian_path_lipschitz f -> is_metric_lipschitz setT F ->
  open U -> U `<=` A ->
  (forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x)) ->
  (forall x, S x -> U (val x)) ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ha) L ->
  is_positive_symmetric_norm_factor (riemannian_tensor_inner hh hb) M -> cancel L I ->
  0<K -> 0<s ->
  (forall x, S x -> forall D : Hom (R_n R m) (R_n R n),
    riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
      (riemannian_tensor_inner hh (set_valP (f x))) n D<=
        K*riemannian_linear_jacobian (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) n D /\
    riemannian_linear_jacobian (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) n D<=
      K*riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
        (riemannian_tensor_inner hh (set_valP (f x))) n D) ->
  (forall x, S x -> riemannian_chart_volume_density hg x<=s*euclidean_det L /\
    euclidean_det L<=s*riemannian_chart_volume_density hg x) ->
  is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S
    (partial_function_precompose (fun x : riemannian_metric_space hg=>L (val x))
      (extended_euclidean_target_jacobian (fun z=>M (F (I z))))) t ->
  (riemannian_jacobian_measure f hp n S<=(K*s)%:E*((euclidean_det L)%:E*t))%E /\
  ((euclidean_det L)%:E*t<=(K*s)%:E*riemannian_jacobian_measure f hp n S)%E.
Proof.
move=> hLip hFLip hU hUA hAgree hSU hS hL hM hLI hK hs hJac hDensity hFrozen.
pose X := [the choiceType of riemannian_metric_space hg].
pose T := [the topologicalType of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)].
pose phi := @riemannian_chart_reference R m A g hg.
pose w := fun x : X=>((riemannian_chart_volume_density hg x)%:E : extended_real_line R).
pose P := partial_density_product (extended_riemannian_map_jacobian f n) (partial_function_total w).
pose Q := partial_function_precompose (fun x : X=>L (val x))
  (extended_euclidean_target_jacobian (fun z=>M (F (I z)))).
pose Qd := partial_extended_function_scale (euclidean_det L) Q.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hDet : 0<euclidean_det L := positive_norm_factor_det_positive hL.
have hKs : 0<K*s := mulr_gt0 hK hs.
have hSource := @riemannian_coarea_reference_subset_integral R m n A B g h hg hh f hp S hLip hS.
have hScaled := @measure_subset_integral_positive_scale R X phi S Q (euclidean_det L) t
  hPhi hDet hFrozen.
pose DF := norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) classical_sets.setT F.
have hDf := @riemannian_reference_function_precompose R m A g hg T DF
  (@euclidean_whole_differential_measurable R m n F hFLip).
have hGraphs : measure_almost_everywhere phi [set x | S x -> exists u v,
    partial_function_graph P x u /\ partial_function_graph Qd x v /\
    (u<=(K*s)%:E*v)%E /\ (v<=(K*s)%:E*u)%E].
  apply:(@measure_almost_everywhere_mono R X phi hPhi _ _ _
    (measurable_function_domain hDf))=> x [D hD] hx.
  have hDifferential := (norm_differential_graph _ _ classical_sets.setT F (val x) D).1 hD.
  have hActualD := (@riemannian_map_differential_local_coordinates R m n A B g h hg hh f U F
    hU hUA hAgree x (hSU x hx) D).2 hDifferential.
  pose j := riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
    (riemannian_tensor_inner hh (set_valP (f x))) n D.
  pose q := riemannian_linear_jacobian (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) n D.
  pose d := riemannian_chart_volume_density hg x.
  pose d0 := euclidean_det L.
  have hJ : partial_function_graph (extended_riemannian_map_jacobian f n) x j%:E.
    exists j; split; last by []; exists D; by split.
  have hQ : partial_function_graph Q x q%:E.
    exact (@frozen_riemannian_coarea_jacobian_graph R m n (g a) (h b)
      (riemannian_tensor_inner hg ha) (riemannian_tensor_inner hh hb) L I M F (val x) D
      hL hM hLI hDifferential).
  have hj0 : 0<=j := riemannian_linear_jacobian_nonnegative _ _ _ _.
  have hq0 : 0<=q := riemannian_linear_jacobian_nonnegative _ _ _ _.
  have hd0 : 0<=d := ltW (@riemannian_chart_volume_density_positive R m A g hg x).
  have hd00 : 0<=d0 := ltW hDet.
  have [hJQ hQJ] := hJac x hx D.
  have [hDD hD0D] := hDensity x hx.
  have hUpper : j*d<=(K*s)*(d0*q).
    have hFirst := ler_wpM2r hd0 hJQ.
    have hSecond := ler_wpM2l (mulr_ge0 (ltW hK) hq0) hDD.
    have hEq : (K*q)*(s*d0)=(K*s)*(d0*q) by ring.
    rewrite -hEq; exact:le_trans hFirst hSecond.
  have hLower : d0*q<=(K*s)*(j*d).
    have hFirst := ler_wpM2r hd00 hQJ.
    have hSecond := ler_wpM2l (mulr_ge0 (ltW hK) hj0) hD0D.
    have hEq : (K*j)*(s*d)=(K*s)*(j*d) by ring.
    rewrite [d0*q]mulrC -hEq; exact:le_trans hFirst hSecond.
  exists (j*d)%:E,(d0*q)%:E; split.
  - apply/partial_density_product_graph; exists j%:E,d%:E; split; first exact hJ.
    split; first by []; by rewrite -EFinM.
  split.
  - exists q%:E; split; first exact hQ; by rewrite -EFinM.
  split; rewrite -EFinM lee_fin; [exact hUpper | exact hLower].
split.
- apply:(@measure_subset_graph_integral_comparison R X phi S P Qd (K*s)
    _ _ hPhi hKs hSource hScaled).
  apply:(@measure_almost_everywhere_mono R X phi hPhi _ _ _ hGraphs)=> x hx hxS.
  have [u [v [hu [hv hBound]]]] := hx hxS; exists u,v; split; first exact hu.
  split; first exact hv; exact:hBound.1.
- apply:(@measure_subset_graph_integral_comparison R X phi S Qd P (K*s)
    _ _ hPhi hKs hScaled hSource).
  apply:(@measure_almost_everywhere_mono R X phi hPhi _ _ _ hGraphs)=> x hx hxS.
  have [u [v [hu [hv hBound]]]] := hx hxS; exists v,u; split; first exact hv.
  split; first exact hu; exact:hBound.2.
Qed.
