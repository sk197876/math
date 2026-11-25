(** Federer (1969), 4.1.5, p. 350:
    the original ball quotient recovers the actual
    density simultaneously for every target vector.
    The numerator is the proved opaque L1 extension,
    and every sufficiently small original characteristic
    function has its full L1 membership. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousDualUP
  WeakEvaluationTopologyUP FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral
  CompactContinuousVectorMeasurable SmoothTestLoneDensity PartialFunctionUP PartialFunctionBasic
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureLpMembershipUP MeasureLpConvergence AbstractDualPartialPairing DualLoneIntegralUP
  DualLoneIntegralSealed DualLoneIntegralLipschitz LoneSeminormContinuityUP DenseLoneExtensionUniqueness
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed MeasureAlmostUP MeasureAlmostBasic
  RadonOpenSubspaceDualBallLimits LoneCharacteristicBallQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionOriginalBallFormula.
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
Local Notation UT := (metric_subset (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable S:Hom DT R^o.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set UT->\bar R.
Variable k:UT->D.
Hypothesis hRepresentation:is_normalised_distribution_representation hD hO dvalues S mu k.
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Let hK:=distribution_representation_weak_measurable hBase.
Let hUnit:=normalised_distribution_density_unit_bound hRepresentation.
Local Notation test := (fun psi:DT=>partial_function_total
  (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY))).
Local Notation I := (@DualLoneIntegral.value R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit).
Let hI:=@DualLoneIntegral.laws R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit.

(** Source for [distribution_original_ball_formula]: the exact
    S(b_(x,r)y)/||S|| B(x,r) formula,
    Federer 4.1.5, p. 350, on one
    conull set for every y. The original
    L1 extension supplies the numerator and its
    domain membership; positive finite denominators
    are derived for all sufficiently small radii. *)
Theorem distribution_original_ball_formula:
  measure_almost_everywhere mu [set x:UT|forall y:Y,forall eta:R,0<eta ->
    exists d:R,0<d /\forall r:R,0<r ->r<d ->
      exists mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass /\
        is_measure_lp_function mu 1 (partial_function_total
          (fun z=>((@CharacteristicFunction.value R UT (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY))) /\
        `|I (partial_function_total
          (fun z=>((@CharacteristicFunction.value R UT (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY)))/mass-ed (k x) y|<eta].
Proof.
have hLimits:=@radon_open_subspace_dual_ball_limits R n U hU Y NY hNY hSep
  D ed DN hD O hO mu hm hr k hK hUnit.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hLimits)=>x hAt y.
exact:(@lone_characteristic_ball_quotient R UT Y NY hNY D ed k mu hm hr I hI x y
  (ed (k x) y) (hAt y)).
Qed.
End DistributionOriginalBallFormula.
