(** Federer (1969), 4.1.4, pp. 348–349: endpoint
    regressions on the actual sealed spaces. They retain
    empty A, dimension zero and the original whole-space
    inward loci when the complement is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP NormOpenDomainLaws
  ContinuousRealFunctional GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual FunctionalSupportUP DistributionDirectionalDerivative EuclideanLebesgueDimensions
  SummableRealFunctionUP MeasureSubsetIntegral NormConvexConnected InnerConvex.
From Federer Require Import CompactDomainDistributionConstancy CompactExhaustionConnectedNeighbourhood CompactTestExtensionLocality ComponentInclusion ConnectedLocalConstancy ConnectedZeroCoordinateQuotients ContinuousDistributionIntegralAction ContinuousDistributionInterchange ContinuousDistributionTestLimit CoordinateZeroConnectedConstancy DirectedOpenCompactCapture DirectedOpenComponentExhaustion DistributionConstancy DistributionConstantDensityAction DistributionDerivativeLocality DomainConstantFunctionalUniqueness GlobalDistributionConstancy GlobalTestVectorIntegral InnerComponentExhaustion InnerComponentFamilyLaws InnerComponentFamilySealed InnerComponentFamilyUP InnerConstantIntegralEvaluation InnerParallelDistanceIdentification InnerParallelFamilyLaws InnerParallelFamilyOpen InnerParallelFamilySealed InnerParallelFamilyUP NormConnectedZeroDifferential OpenDomainDistributionConstancy PositiveNormLimitUP RegularisationConstantRepresentation RegularisationConstantScaleIndependence SmoothedDistributionInnerConstancy SmoothedDistributionInwardDerivativeZero SmoothedKernelDensityFamily SmoothedKernelIntegralFamily TestDirectionalValues TestScalarSubsetIntegral TestZeroExtensionDirectional TestZeroExtensionRange TranslatedKernelExactSupport TranslatedKernelTestDirectional TranslatedKernelUnitMass VectorIntegralTotalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ActualEmptyDomain.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Local Notation E := (@SmoothFunctionSpace.space R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation ev := (@SmoothFunctionSpace.value R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation hE := (@SmoothFunctionSpace.laws R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation D := (@SmoothFunctionDerivatives.operators R X Y N NY hN hNY (fun _=>True) E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X Y N NY hN hNY (fun _=>True) E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE)).

(** Source for [empty_open_constancy_regression]: the empty-A
    boundary of Federer 4.1.4, p. 348, is valid for every
    actual distribution, without a dimension restriction. *)
Theorem empty_open_constancy_regression (T:DD):
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` set0 ->
      is_measure_subset_integral (@euclidean_lebesgue_measure R n) setT
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (eD T f)%:E.
Proof.
apply:(@distribution_derivative_support_constant R n Y NY hNY hY E ev (fun _=>True) hFull hE D hD
  T set0 (@open0 (real_norm_metric_space hN)) (@connected0 (real_norm_metric_space hN)) (fun _ _=>Logic.I)).
by move=>i x hx; split.
Qed.
End ActualEmptyDomain.
Section ActualZeroSource.
Variable R:realType.
Local Notation X := (R_n R 0).
Local Notation N := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Local Notation E := (@SmoothFunctionSpace.space R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation ev := (@SmoothFunctionSpace.value R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation hE := (@SmoothFunctionSpace.laws R X Y N NY hN hNY (fun _=>True) hFull).
Local Notation D := (@SmoothFunctionDerivatives.operators R X Y N NY hN hNY (fun _=>True) E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X Y N NY hN hNY (fun _=>True) E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).

(** Source for [zero_source_distribution_constancy_regression]:
    with no coordinate derivative hypotheses in R^0, every
    actual distribution has the original constant-functional
    integral representation, Federer 4.1.4, pp. 348–349. *)
Theorem zero_source_distribution_constancy_regression (T:DD):
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,is_measure_subset_integral (@euclidean_lebesgue_measure R 0) setT
      (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (eD T f)%:E.
Proof.
have hConvex:is_inner_convex (@setT X) by move=>x y _ _ t _ _.
have hConnected:=@norm_inner_convex_connected R X N hN setT hConvex.
have hSupport:forall i:'I_0,forall x,
    @smooth_functional_support R X Y N hN (fun _=>True) DT (smooth_test_value hE)
      (eD (@distribution_directional_derivative R X Y N NY hN hNY (fun _=>True) hFull E ev hE D hD
        (@coordinate_basis R 0 i) T)) x ->True /\ ~True.
  move=>i; by move:(valP i); rewrite ltn0.
have[alpha [hAlpha hRep]]:=@distribution_derivative_support_constant R 0 Y NY hNY hY E ev
  (fun _=>True) hFull hE D hD T setT (@openT (real_norm_metric_space hN)) hConnected
  (fun _ _=>Logic.I) hSupport.
exists alpha; split=>// f; exact:(hRep f (fun _ _=>Logic.I)).
Qed.
End ActualZeroSource.

(** Source for [whole_space_inner_component_regression]: if A
    is all R^n, its complement is empty and every original
    inward component is all R^n, at every positive radius.
    This checks the empty-complement convention in the proof
    of Federer 4.1.4, pp. 348–349. *)
Theorem whole_space_inner_component_regression (R:realType) n (a:R_n R n) e:0<e ->
  @InnerComponentFamily.value R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@InnerParallelFamily.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n)) setT) a e=setT.
Proof.
move=>he.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose NT:=real_norm_metric_space hN.
pose O:=@InnerParallelFamily.value R X N setT.
pose hO:=@InnerParallelFamily.laws R X N setT.
have hWhole:O e=setT.
  apply:funext=>x; apply:propext; split=>// _.
  apply:(@hO e he x).2; split; first exact Logic.I.
  exists (e+1); split; first by lra.
  by move=>y _.
rewrite (@InnerComponentFamily.laws R NT O a e he) hWhole.
apply:(@connected_component_id NT setT a Logic.I).
apply:(@norm_inner_convex_connected R X N hN setT).
by move=>x y _ _ t _ _.
Qed.
