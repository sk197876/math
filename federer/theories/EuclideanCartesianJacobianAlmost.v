(** Federer (1969), 3.2.23, p. 260: the product of two
    exact ordinary-Jacobian representatives agrees almost everywhere
    with the actual top Jacobian of f times g. Rademacher and the
    actual product differential discharge the exceptional points. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianLinear EuclideanCartesianDifferential
  EuclideanCartesianAlmost EuclideanLinearJacobian Jacobian JacobianUP EuclideanJacobianMeasurable
  LipschitzUP Rademacher NormDifferentialUP EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureUP
  MeasureAlmostUP MeasureAlmostBasic RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_cartesian_jacobian_almost]: the product
    Jacobian equality used under the integral in Federer 3.2.23,
    p. 260. This is almost equality of actual partial functions;
    it does not declare a Jacobian value at a nondifferentiability
    point. Auxiliary representatives agree with every actual factor
    differential, as supplied by the existing Borel representative laws. *)
Theorem euclidean_cartesian_jacobian_almost (R:realType) m mu n v
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (g:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v))
    (J:R_n R m->R) (K:R_n R mu->R):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT g ->
  (forall x A,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x A ->J x=euclidean_linear_jacobian m A) ->
  (forall y B,has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R v)) setT g y B ->K y=euclidean_linear_jacobian mu B) ->
  measure_almost_equal (@euclidean_lebesgue_measure R (m+mu))
    (extended_euclidean_jacobian (euclidean_cartesian_map f g))
    (partial_function_total (fun p:R_n R (m+mu)=>
      ((J (euclidean_block_split p).1*K (euclidean_block_split p).2)%R%:E:extended_real_line R))).
Proof.
move=>hF hG hJ hK.
have hBoth:=euclidean_cartesian_almost_everywhere_factors (federer_3_1_6 hF) (federer_3_1_6 hG).
apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R (m+mu)) _ hBoth)=>p [[A hA] [B hB]].
exists ((J (euclidean_block_split p).1*K (euclidean_block_split p).2)%:E:extended_real_line R).
split; last by [].
exists (J (euclidean_block_split p).1*K (euclidean_block_split p).2)%R; split; last by [].
apply:(euclidean_jacobian_graph (m+mu) setT (euclidean_cartesian_map f g) p _).2.
exists (euclidean_cartesian_linear A B); split; first exact:(euclidean_cartesian_differential hA hB).
by rewrite euclidean_cartesian_linear_jacobian -(hJ _ _ hA) -(hK _ _ hB).
Qed.
