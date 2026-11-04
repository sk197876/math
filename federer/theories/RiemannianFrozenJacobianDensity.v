(** Federer (1969), 3.2.46, p. 282: local frozen
    metric comparisons pass from actual exterior Jacobians
    to their area density measures. This supporting step
    preserves arbitrary source subsets and infinite masses;
    Rademacher supplies the actual common differential domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness OperatorNorm NormDifferentialUP NormDifferential
  NormDifferentialFiniteCalculus EuclideanLinearMaps EuclideanLinearJacobian
  Jacobian JacobianDensityMeasure EuclideanJacobianMeasurable
  RiemannianTensorUP RiemannianLinearJacobian RiemannianJacobianVolumeFactor
  RiemannianTargetJacobian PositiveSymmetricNormFactor ExteriorMetricComparison
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensityUP MeasureDensity
  MeasureDensityLocalComparison MeasureStepIntegralIdentification ExtendedRealOrderTopology
  EuclideanLebesgueDimensions LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [frozen_riemannian_area_density_bounds]: the
    local frozen-L argument for 3.2.46, p. 282, at
    the level of the actual area upper integrals. Independent
    vector comparisons on the original image patch imply both
    lambda^m density bounds; no Jacobian identity, rank condition
    or integrability premise is supplied. *)
Theorem frozen_riemannian_area_density_bounds (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : R_n R m -> R_n R n) (hf : forall x, A (f x)) o (ho : A o)
    (L : {linear R_n R n -> R_n R n}) (lambda : R) (S : set (R_n R m)) :
  @is_metric_lipschitz R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT f ->
  0<lambda -> is_positive_symmetric_norm_factor (riemannian_tensor_inner hh ho) L ->
  (forall x, S x -> forall v,
    inner_norm (riemannian_tensor_inner hh ho) v<=
      lambda*inner_norm (riemannian_tensor_inner hh (hf x)) v /\
    inner_norm (riemannian_tensor_inner hh (hf x)) v<=
      lambda*inner_norm (riemannian_tensor_inner hh ho) v) ->
  (euclidean_jacobian_measure (fun x=>L (f x)) S<=
    (lambda^+m)%:E*measure_with_density (@euclidean_lebesgue_measure R m)
      (@extended_target_riemannian_jacobian R m n A h hh f hf m) S)%E /\
  (measure_with_density (@euclidean_lebesgue_measure R m)
      (@extended_target_riemannian_jacobian R m n A h hh f hf m) S<=
    (lambda^+m)%:E*euclidean_jacobian_measure (fun x=>L (f x)) S)%E.
Proof.
move=> hLip hLambda hL hVectors.
pose phi := @euclidean_lebesgue_measure R m.
pose X := [the choiceType of inner_metric_space (@euclidean_inner_productP R m)].
pose F := extended_euclidean_jacobian (fun x=>L (f x)).
pose G := @extended_target_riemannian_jacobian R m n A h hh f hf m.
pose mu := euclidean_jacobian_measure (fun x=>L (f x)).
pose nu := measure_with_density phi G.
have hPhi := euclidean_lebesgue_is_measure R m.
have hMu := euclidean_jacobian_measure_laws (fun x=>L (f x)).
have hNu := measure_with_density_laws phi G.
have hPower : 0<lambda^+m := exprn_gt0 m hLambda.
have hLinear : norm_bounded_linear (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) (hom_of_linear L).
  exists (linear_operator_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
    (@coordinate_basisP R n) L); split.
  - exact: linear_operator_norm_nonnegative.
  - move=> v; exact (linear_operator_norm_bound (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) L v).
have hCompare : measure_almost_everywhere phi
    [set x | exists u v, partial_function_graph F x u /\ partial_function_graph G x v /\
      (S x -> (u<=(lambda^+m)%:E*v)%E /\ (v<=(lambda^+m)%:E*u)%E)].
  apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _ (federer_3_1_6 hLip))=> x [D hD].
  pose q := euclidean_linear_jacobian m (hom_comp (hom_of_linear L) D).
  pose j := riemannian_linear_jacobian (@euclidean_inner_productP R m)
    (riemannian_tensor_inner hh (hf x)) m D.
  have hLD := @norm_differential_postcompose R (R_n R m) (R_n R n) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) setT f x D (hom_of_linear L) hD hLinear.
  have hF : partial_function_graph F x q%:E.
    exists q; split; last by [].
    apply: (euclidean_jacobian_graph m setT (fun x=>L (f x)) x q).2.
    exists (hom_comp (hom_of_linear L) D); by split.
  have hG : partial_function_graph G x j%:E.
    exists j; split; last by [].
    apply: (@target_riemannian_jacobian_graph R m n A h hh f hf m x j).2.
    exists D; by split.
  exists q%:E,j%:E; split; first exact hF; split; first exact hG.
  move=> hx.
  have hBounds : q<=lambda^+m*j /\ j<=lambda^+m*q.
    rewrite /q -(@riemannian_jacobian_target_coordinates R m n (h o)
      (riemannian_tensor_inner hh ho) L m D hL).
    split.
    - exact (@exterior_operator_target_metric_comparison R (euclidean_two_nonzero R)
        (R_n R m) (R_n R n) (@euclidean_inner_product R m) (h (f x)) (h o)
        (@euclidean_inner_productP R m) (riemannian_tensor_inner hh (hf x))
        (riemannian_tensor_inner hh ho) n (@coordinate_basis R n) (@coordinate_basisP R n)
        (hom_as_linear D) lambda m _ _ (ltW hLambda) (fun v=>(hVectors x hx v).1)
        (riemannian_linear_jacobian_laws (@euclidean_inner_productP R m)
          (riemannian_tensor_inner hh (hf x)) m D)
        (riemannian_linear_jacobian_laws (@euclidean_inner_productP R m)
          (riemannian_tensor_inner hh ho) m D)).
    - exact (@exterior_operator_target_metric_comparison R (euclidean_two_nonzero R)
        (R_n R m) (R_n R n) (@euclidean_inner_product R m) (h o) (h (f x))
        (@euclidean_inner_productP R m) (riemannian_tensor_inner hh ho)
        (riemannian_tensor_inner hh (hf x)) n (@coordinate_basis R n) (@coordinate_basisP R n)
        (hom_as_linear D) lambda m _ _ (ltW hLambda) (fun v=>(hVectors x hx v).2)
        (riemannian_linear_jacobian_laws (@euclidean_inner_productP R m)
          (riemannian_tensor_inner hh ho) m D)
        (riemannian_linear_jacobian_laws (@euclidean_inner_productP R m)
          (riemannian_tensor_inner hh (hf x)) m D)).
  split; rewrite -EFinM lee_fin; [exact hBounds.1 | exact hBounds.2].
split.
- apply: (@measure_density_local_graph_comparison R X phi mu nu F G S (lambda^+m)
    hPhi hMu hNu hPower).
  apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _ hCompare)=> x [u [v [hu [hv hBound]]]].
  exists u,v; split; first exact hu; split; first exact hv.
  move=> hx; exact: (hBound hx).1.
- apply: (@measure_density_local_graph_comparison R X phi nu mu G F S (lambda^+m)
    hPhi hNu hMu hPower).
  apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _ hCompare)=> x [u [v [hu [hv hBound]]]].
  exists v,u; split; first exact hv; split; first exact hu.
  move=> hx; exact: (hBound hx).2.
Qed.
