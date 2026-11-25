(** Federer (1969), 4.1.5, p. 350:
    the original normalized representation gives a
    unique continuous extension to the whole L1
    space, and actual tests are dense there.
    Compact scalar integrability is discharged from
    the original gauge, not assumed separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousDualUP
  WeakEvaluationTopologyUP FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral
  CompactContinuousVectorMeasurable SmoothTestLoneDensity PartialFunctionUP PartialFunctionBasic
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureLpMembershipUP MeasureLpConvergence AbstractDualPartialPairing DualLoneIntegralUP
  DualLoneIntegralSealed DualLoneIntegralLipschitz LoneSeminormContinuityUP DenseLoneExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionLoneExtension.
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
Let F:=@normalised_distribution_scalar_integral R UT Y NY hNY D ed DN hD O hO
  DT dvalues S mu k hRepresentation.
Let hF:=@normalised_distribution_scalar_integral_laws R UT Y NY hNY D ed DN hD O hO
  DT dvalues S mu k hRepresentation.
Local Notation test := (fun psi:DT=>partial_function_total
  (fun x:UT=>(dvalues psi x:real_norm_metric_space hNY))).
Local Notation I := (@DualLoneIntegral.value R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit).
Let hI:=@DualLoneIntegral.laws R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit.

(** Source for [distribution_original_test_lone_member]:
    every actual test is in the original variation
    L1 space, Federer 4.1.5, p. 350. *)
Lemma distribution_original_test_lone_member (psi:DT):
  is_measure_lp_function mu 1 (test psi).
Proof.
have hTest:=@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE psi.
exact:(@compact_continuous_vector_lone_member R UT Y NY hNY hSep mu hm hr F hF (dvalues psi) hTest).
Qed.

(** Source for [distribution_original_test_lone_dense]:
    actual D(U,Y) is dense in the original
    L1 seminorm, Federer 4.1.5, p. 350,
    for every conull partial function. *)
Theorem distribution_original_test_lone_dense (f:partial_function UT (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->forall epsilon:R,0<epsilon ->
  exists psi:DT,is_measure_lp_function mu 1 (test psi) /\
    (measure_lp_distance mu NY 1 f (test psi)<epsilon%:E)%E.
Proof.
exact:(@smooth_test_lone_dense R n Y NY hNY hY hSep U hU E ev hE mu hm hr F hF f).
Qed.

(** Source for [distribution_lone_extension_agrees]:
    the opaque L1 integral agrees with S
    on every original test, Federer 4.1.5,
    p. 350. *)
Theorem distribution_lone_extension_agrees (psi:DT):I (test psi)=S psi.
Proof.
have hIntegral:=@hI (test psi) (distribution_original_test_lone_member psi).
have hTotal:=measure_integral_graph_equivalent
  (@abstract_dual_partial_pairing_total_graph R UT Y D ed k (dvalues psi)) hIntegral.
have hOriginal:=distribution_representation_action hBase psi.
have hEq:=measure_integral_unique hTotal hOriginal.
by injection hEq.
Qed.

(** Source for [distribution_lone_extension_lipschitz]:
    the extension has norm at most one in
    the original L1 seminorm, Federer 4.1.5,
    p. 350, with all partial domains retained. *)
Theorem distribution_lone_extension_lipschitz (f g:partial_function UT (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f ->is_measure_lp_function mu 1 g ->
  (`|I f-I g|%:E<=measure_lp_distance mu NY 1 f g)%E.
Proof.
exact:(@dual_lone_integral_lipschitz R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit I hI f g).
Qed.

(** Source for [distribution_lone_extension_continuous]:
    the stated original L1 continuity of the
    integral extension, Federer 4.1.5, p. 350. *)
Theorem distribution_lone_extension_continuous:
  @is_lone_seminorm_continuous R UT Y NY hNY mu I.
Proof.
exact:(@dual_lone_integral_continuity R UT Y NY hNY hSep D ed DN hD O hO mu hm k hK hUnit I hI).
Qed.

(** Source for [distribution_lone_extension_unique]:
    agreement on actual tests and original L1
    continuity uniquely determine the extension,
    Federer 4.1.5, p. 350. *)
Theorem distribution_lone_extension_unique
    (J:partial_function UT (real_norm_metric_space hNY)->R):
  @is_lone_seminorm_continuous R UT Y NY hNY mu J ->
  (forall psi:DT,J (test psi)=S psi) ->
  forall f,is_measure_lp_function mu 1 f ->I f=J f.
Proof.
move=>hJ hAgreement.
apply:(@dense_lone_extension_unique R UT Y NY hNY mu hm DT test I J
  distribution_lone_extension_lipschitz hJ distribution_original_test_lone_dense).
by move=>psi; rewrite distribution_lone_extension_agrees hAgreement.
Qed.
End DistributionLoneExtension.
