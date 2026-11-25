(** Federer (1969), 4.1.7, p. 358: compare
    the two bounded dual densities after scalar
    domination. Actual test density in L1, proved
    in 4.1.5, p. 350, extends their agreement
    to all original L1 fields. No representing
    measure identity is assumed in this adapter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousDualUP WeakEvaluationTopologyUP OpenFamilyTopologyMathcomp VectorDaniellHypotheses
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionSubspaceTestValues FunctionLatticeUP CompactSupportFunctionUP
  CompactContinuousVectorMeasurable RadonCompactScalarIntegral RealIntegralFunctionalUP
  PartialFunctionUP PartialFunctionBasic MeasureUP RadonMeasureUP MeasureLpMembershipUP
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  SummableRealFunctionUP AbstractDualPartialPairing DualLoneIntegralUP DualLoneIntegralSealed
  DualLoneIntegralLipschitz LoneSeminormContinuityUP SmoothTestLoneDensity DenseLoneExtensionUniqueness
  DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BoundedDualTestDensity.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT := (set_type (U:set XT)).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation test := (fun psi:DT=>partial_function_total
  (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY))).
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variables a b:UT->D.
Hypothesis hA:is_measure_measurable_function mu
  (partial_function_total (fun x=>(a x:open_family_topological_space hO.1))).
Hypothesis hB:is_measure_measurable_function mu
  (partial_function_total (fun x=>(b x:open_family_topological_space hO.1))).
Hypothesis hAUnit:forall x,DN (a x)<=1.
Hypothesis hBUnit:forall x,DN (b x)<=1.
Variable S:Hom DT R^o.
Hypothesis hAAction:is_distribution_integral_action mu ed a dvalues S.
Hypothesis hBAction:is_distribution_integral_action mu ed b dvalues S.
Local Notation I := (@DualLoneIntegral.value R UT Y NY hNY hSep D ed DN hD O hO mu hm a hA hAUnit).
Local Notation J := (@DualLoneIntegral.value R UT Y NY hNY hSep D ed DN hD O hO mu hm b hB hBUnit).
Local Notation F := (@radon_positive_compact_integral R UT mu hm hr).
Local Notation hF := (@radon_positive_compact_integral_laws R UT mu hm hr).

(** Source for [bounded_dual_test_lone_integrals_equal]:
    bounded densities agreeing on every actual
    test agree on all original L1 integrals,
    supporting Federer 4.1.7, p. 358, by
    the proved density and extension uniqueness
    assertions of 4.1.5, p. 350. *)
Theorem bounded_dual_test_lone_integrals_equal f:
  is_measure_lp_function mu 1 f ->I f=J f.
Proof.
have hI:=@DualLoneIntegral.laws R UT Y NY hNY hSep D ed DN hD O hO mu hm a hA hAUnit.
have hJ:=@DualLoneIntegral.laws R UT Y NY hNY hSep D ed DN hD O hO mu hm b hB hBUnit.
have hLipschitz:=@dual_lone_integral_lipschitz R UT Y NY hNY hSep D ed DN hD O hO
  mu hm a hA hAUnit I hI.
have hContinuous:@is_lone_seminorm_continuous R UT Y NY hNY mu J.
  exact:(@dual_lone_integral_continuity R UT Y NY hNY hSep D ed DN hD O hO
    mu hm b hB hBUnit J hJ).
have hDense:=@smooth_test_lone_dense R n Y NY hNY hY hSep U hU E ev hE mu hm hr F hF.
have hAgreement psi:I (test psi)=J (test psi).
  have hTest:=@smooth_test_original_continuous_field R X Y NX NY hNX hNY U E ev hE psi.
  have hMember:=@compact_continuous_vector_lone_member R UT Y NY hNY hSep mu hm hr F hF
    (dvalues psi) hTest.
  have hIA:=measure_integral_graph_equivalent
    (@abstract_dual_partial_pairing_total_graph R UT Y D ed a (dvalues psi)) (@hI (test psi) hMember).
  have hJB:=measure_integral_graph_equivalent
    (@abstract_dual_partial_pairing_total_graph R UT Y D ed b (dvalues psi)) (@hJ (test psi) hMember).
  have hIEqual:=measure_integral_unique hIA (hAAction psi).
  have hJEqual:=measure_integral_unique hJB (hBAction psi).
  have hIValue:I (test psi)=S psi by injection hIEqual.
  have hJValue:J (test psi)=S psi by injection hJEqual.
  by rewrite hIValue hJValue.
exact:(@dense_lone_extension_unique R UT Y NY hNY mu hm DT test I J
  hLipschitz hContinuous hDense hAgreement f).
Qed.
End BoundedDualTestDensity.
