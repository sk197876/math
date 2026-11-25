(** Federer (1969), 4.1.7, p. 357: the
    original exact-domain orienting field is measurable,
    has mass one almost everywhere and represents
    the current. The earlier simultaneous ball formula
    identifies it with the normalized density of
    4.1.5 without shrinking its original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual NormalisedCurrentSealed
  CurrentOriginalBallFormula MultivectorDualSealed PartialFunctionUP PartialFunctionBasic
  PartialFunctionPair PartialFunctionPostcomposition MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureLpMembershipUP MeasurableFunctionUP MeasurableAlmostModification MeasureIntegralUP
  MeasureIntegralAlmostEquality SummableRealFunctionUP OpenFamilyTopologyMathcomp
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PositiveScalarGraphLimit
  CurrentBallLimitsUP CurrentOrientationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentOrientationAlmost.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (metric_subset (U:set (real_norm_metric_space hNX))).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation k := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu k hRepresentation).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation P := (@CurrentOrientation.value R h2 n m U hU T hT).
Local Notation hP := (@CurrentOrientation.laws R h2 n m U hU T hT).
Local Notation F := (@current_ball_characteristic_field R h2 n m U).

(** Source for [current_orientation_normalised_agreement]:
    the original maximal orienting field agrees
    almost everywhere with the normalized Radon
    density, Federer 4.1.7, p. 357,
    using the simultaneous formula from 4.1.5. *)
Theorem current_orientation_normalised_agreement:
  measure_almost_everywhere mu [set x:UT|partial_function_graph P x (k x)].
Proof.
have hBall:=@current_original_ball_formula R h2 n m U hU T mu k hRepresentation.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hBall)=>x hx.
apply:(hP.2 x (k x)).2=>y eta hEta.
have[d [hd hSmall]]:=hx y eta hEta.
exists d;split=>//r hr hrd.
have[mass [hMass [hPositive [hMember hError]]]]:=hSmall r hr hrd.
exists (I (F y x r)/mass);split;last exact:hError.
split;first exact:hr.
exists mass;by split=>//;split=>//;split.
Qed.

(** Source for [current_orientation_domain_conull]:
    the original maximal domain is conull,
    supporting the measurability assertion in
    Federer 4.1.7, p. 357. *)
Theorem current_orientation_domain_conull:
  measure_almost_everywhere mu (partial_function_domain P).
Proof.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _
  current_orientation_normalised_agreement)=>x hx.
by exists (k x).
Qed.

(** Source for [current_orientation_unit_mass]:
    the original orienting field has mass one
    almost everywhere, Federer 4.1.7, p. 357.
    The assertion retains its actual partial graph. *)
Theorem current_orientation_unit_mass:
  measure_almost_everywhere mu [set x:UT|exists v:V,
    partial_function_graph P x v /\DN v = 1].
Proof.
have hBoth:=@measure_almost_everywhere_and R UT mu hm _ _
  current_orientation_normalised_agreement
  (normalised_distribution_density_unit_norm hRepresentation).
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hBoth)=>x [hGraph hMass].
by exists (k x).
Qed.

(** Source for [current_orientation_weak_measurable]:
    measurability of the original exact-domain
    field in the weak multivector topology,
    Federer 4.1.7, p. 357. The earlier
    almost-equal partial-function theorem applies. *)
Theorem current_orientation_weak_measurable:
  is_measure_measurable_function mu
    (P:partial_function UT (open_family_topological_space hO.1)).
Proof.
apply:(@measurable_function_almost_equal R UT (open_family_topological_space hO.1)
  mu hm (partial_function_total (fun x=>(k x:open_family_topological_space hO.1))) P
  (distribution_representation_weak_measurable hBase)).
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _
  current_orientation_normalised_agreement)=>x hx.
exists (k x);by split.
Qed.

Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_oriented_test_pairing]:
    the original pairing of the partial orienting
    field with an actual compact test form,
    Federer 4.1.7, p. 357. It is
    defined exactly on the field's domain. *)
Definition current_oriented_test_pairing (phi:DT):partial_function UT (\bar R):=
  partial_function_postcompose (partial_function_pair P (partial_function_total (dvalues phi)))
    (fun vy=>(ed vy.1 vy.2)%:E).

(** Source for [current_orientation_integral_action]:
    S(phi) is the integral of the
    original orienting-field pairing against ||S||,
    Federer 4.1.7, p. 357. The
    equality uses the actual partial integrand. *)
Theorem current_orientation_integral_action phi:
  is_measure_integral mu (current_oriented_test_pairing phi) (action T phi)%:E.
Proof.
apply:(@measure_integral_almost_equal R UT mu hm
  (real_total_integrand (fun x=>ed (k x) (dvalues phi x)))
  (current_oriented_test_pairing phi) (action T phi)%:E
  (distribution_representation_action hBase phi)).
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _
  current_orientation_normalised_agreement)=>x hx.
exists (ed (k x) (dvalues phi x))%:E;split;first by rewrite real_total_integrand_graph.
exists (k x,dvalues phi x);split;first by split.
by [].
Qed.
End CurrentOrientationAlmost.
