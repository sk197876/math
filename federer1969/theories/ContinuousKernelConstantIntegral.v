(** Federer (1969), 4.1.3, p. 348, using 4.1.2,
    p. 347: an actual compact smooth kernel integrates a fixed
    vector with its scalar mass. Only the continuous integrand's
    actual range is needed; Y may be a nonseparable Banach space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormRegularity
  NormRegularityOperations NormOpenDomainLaws NormClassZeroScalarProduct
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormMetricCompactness SmoothCompactSet ContinuousCompactFieldIntegral
  PartialFunctionBasic SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureVectorIntegralUP
  WeakDerivativeFieldVectorIntegral ContinuousRealFunctional EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_kernel_constant_integral]: the actual
    unit-kernel identity used for test approximation in Federer
    4.1.3, p. 348, with arbitrary scalar kernel mass included. *)
Theorem continuous_kernel_constant_integral (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (psi:R_n R n->R) r a (y:Y):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) psi ->
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->psi z=0) ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand psi) a%:E ->
  is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(psi z*:y:real_norm_metric_space hNY))) (a*:y).
Proof.
move=>hPsi hOff hScalar.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set x|N x<=r] (fun _ _=>I)
  (@finite_norm_metric_ball_compact R X N hN n (@coordinate_basis R n) (@coordinate_basisP R n) r).
have hConst:=@norm_class_constant R X Y N NY hN hNY (fun _=>True) y 0%N
  (fun x _=>norm_full_domain_interior N x).
have hCont:=@norm_class_zero_scalar_product R X Y N NY hNY (fun _=>True)
  psi (fun _=>y) (norm_class_continuous (hPsi 0%N)) (norm_class_continuous hConst).
have hZero z:~smooth_compact_carrier K z ->psi z*:y=0.
  move=>hz; have hLarge:r<N z by rewrite ltNge; apply/negP=>h; exact:hz h.
  by rewrite (hOff z hLarge) scale0r.
have[v hI]:=@continuous_compact_field_integral_exists R n Y NY hNY hY _ K hCont hZero.
have hValue:v=a*:y.
  apply:(@continuous_real_functionals_separate R Y NY hNY v (a*:y))=>alpha hAlpha.
  have h:=hI.2 alpha hAlpha.
  have hScaled:=@real_total_integral_scale R X mu (euclidean_lebesgue_is_measure R n)
    psi a (alpha y) hScalar.
  have hSame:is_measure_integral mu
      (partial_functional_evaluation (partial_function_total (fun z=>(psi z*:y:real_norm_metric_space hNY))) alpha)
      (alpha (a*:y))%:E.
    have hA:alpha (a*:y)=a*alpha y by rewrite linearZ.
    rewrite hA mulrC.
    apply:(measure_integral_graph_equivalent _ hScaled)=>z t.
    have hPoint:alpha (psi z*:y)=psi z*alpha y by rewrite linearZ.
    by rewrite total_functional_evaluation_graph real_total_integrand_graph hPoint mulrC.
  have hEq:=measure_integral_unique h hSame.
  by injection hEq.
by rewrite -hValue.
Qed.
