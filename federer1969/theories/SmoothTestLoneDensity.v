(** Federer (1969), 4.1.5, p. 350:
    the actual D(U,Y) is dense in the original
    vector L1 seminorm. First use compact continuous
    L1 approximation, then the actual smooth convolution
    approximation. The earlier almost-equality laws
    restore every original conull partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses
  CompactContinuousVectorFields CompactContinuousLoneDensity CompactContinuousVectorMeasurable
  CompactContinuousTestLoneApproximation SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationDomain DistributionSubspaceTestValues
  MeasureUP RadonMeasureUP RealIntegralFunctionalUP PartialFunctionUP PartialFunctionBasic
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureLpMembershipUP MeasureLpAlmostEquality
  MeasureLpConvergence MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  SeparableVectorLone VectorLoneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothTestLoneDensity.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable F:(UT->R)->R.
Hypothesis hF:is_real_integral_functional mu
  (positive_function_lattice (@compactly_supported_continuous_functions R UT)) F.

(** Source for [smooth_test_lone_total_dense]:
    every total original L1 function has actual
    compact smooth test approximants with arbitrarily
    small finite integral norm error, Federer 4.1.5,
    p. 350. *)
Theorem smooth_test_lone_total_dense (f:UT->real_norm_metric_space hNY):
  is_measure_lp_function mu 1 (partial_function_total f) ->
  forall epsilon:R,0<epsilon ->exists psi:DT,exists a:R,
    is_measure_integral mu (real_total_integrand (fun x=>NY (f x-dvalues psi x))) a%:E /\
    a<epsilon.
Proof.
move=>hf epsilon hEpsilon.
have hHalf:0<epsilon/2 by rewrite divr_gt0 // ltr0n.
have hContinuousDensity:=@compact_continuous_vector_lone_dense R UT Y NY hNY hSep mu hm hr F hF f hf.
have[w [a [hw [hA hASmall]]]]:=hContinuousDensity (epsilon/2) hHalf.
have[psi [b [hB hBSmall]]]:=@compact_continuous_field_test_lone_approximation R n Y NY hNY hY U hU E ev hE
  mu hm hr F hF w hw (epsilon/2) hHalf.
have hTest:=@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE psi.
have hTestMeasurable:=@compact_continuous_vector_normed_measurable R UT Y NY hNY hSep mu hm hr (dvalues psi) hTest.
have[c [hC hCBound]]:=@vector_norm_error_transfer_integral R UT Y NY hNY mu hm f w (dvalues psi) a b
  hf.2.1 hTestMeasurable hA hB.
exists psi,c; split=>//.
have hSum:a+b<epsilon by lra.
exact:le_lt_trans hCBound hSum.
Qed.

(** Source for [smooth_test_lone_dense]:
    D(U,Y) is dense in the original L1
    seminorm, Federer 4.1.5, p. 350,
    for every original conull partial function.
    Actual test L1 membership is included and
    no positive total-mass premise is added. *)
Theorem smooth_test_lone_dense (f:partial_function UT (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->
  forall epsilon:R,0<epsilon ->exists psi:DT,
    is_measure_lp_function mu 1
      (partial_function_total (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY))) /\
    (measure_lp_distance mu NY 1 f
      (partial_function_total (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY)))<epsilon%:E)%E.
Proof.
move=>hf epsilon hEpsilon.
have[g [hExtension [hAlmost hGMeasurable]]]:=@measurable_normed_total_representative R UT Y NY hNY mu hm f hf.2.1.
have hG:=@measure_lp_function_almost_equal R UT Y NY hNY mu hm 1 f (partial_function_total g) hf hAlmost.
have[psi [a [hI hSmall]]]:=smooth_test_lone_total_dense hG hEpsilon.
have hTest:=@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE psi.
have hTestLone:=@compact_continuous_vector_lone_member R UT Y NY hNY hSep mu hm hr F hF (dvalues psi) hTest.
exists psi; split; first exact hTestLone.
have hDistance:=@total_vector_lone_distance_integral R UT Y NY hNY mu hm g (dvalues psi) hGMeasurable hTestLone.2.1.
have hEq:=measure_integral_unique hDistance hI.
rewrite (@measure_lp_distance_almost_left R UT Y NY hNY mu hm 1 f (partial_function_total g)
  (partial_function_total (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY))) (lexx _) hf.2.1
  hGMeasurable hTestLone.2.1 hAlmost) hEq lte_fin.
exact hSmall.
Qed.
End SmoothTestLoneDensity.
