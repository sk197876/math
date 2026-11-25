(** Federer (1969), 4.1.7, p. 359:
    the original projection formula for every
    bounded Baire form. The actual measurable
    current contractions are compared on genuine
    tests through the exact weighted image
    measure and the preceding L1 extension.
    Properness is imposed only on spt T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import CurrentEvaluation Hom TensorUP ScalarCoefficients RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingProduct AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  NormalisedCurrentSealed CurrentImageDensityPairing CurrentImageWeightRadon CurrentProperSupport
  CurrentProperSupportDomain CurrentProperSupportRestriction CurrentProperPullbackTests CurrentPushforwardUP
  CurrentPushforwardSealed CurrentPushforwardWeight CurrentPushforwardVariation CurrentPushforwardWeightedLone
  CurrentMeasurableProducts CurrentMeasurableProductCoefficients CurrentMeasurableMultiplierUP
  CurrentMeasurableMultiplierSupport CurrentBaireFormPullback CurrentFormPullbackOnDomain
  CurrentBaireTestProductLone CurrentBaireTestSourceMeasurable CurrentBaireProjectionPairing BoundedBaireFieldLocalIntegral
  SmoothFormPullbackSealed SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSupport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP AbstractDualPartialPairing
  WeightedDualTotalPairing OpenFamilyTopologyMathcomp BaireFunctions PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureDensity
  RadonMeasureUP MeasurableFunctionUP MeasureLpMembershipUP SummableRealFunctionUP CurrentRadonSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardBaireProjection.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k p:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Local Notation A := (A_m Y R^o (k+p)).
Local Notation AN := (@current_form_comass R h2 n (k+p)).
Local Notation hAN := (@current_form_comass_real_norm R h2 n (k+p)).
Local Notation D := (exterior_power Y (k+p)).
Local Notation DN := (@current_vector_mass R h2 n (k+p)).
Local Notation ed := (@MultivectorDual.evaluation R Y (k+p)).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n (k+p)).
Local Notation O := (@current_multivector_weak_opens R n (k+p)).
Local Notation hO := (@current_multivector_weak_laws R n (k+p)).
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n V hV d).
Local Notation fv := (fun d=>@current_smooth_value R h2 v U hU d).
Local Notation ev := (fun d=>@current_test_value R h2 n V hV d).
Local Notation DU := (@current_test_space R h2 v U hU p).
Local Notation DV := (@current_test_space R h2 n V hV p).
Variable T:@current_space R h2 v U hU (k+p).
Hypothesis hT:@is_integration_representable_current R h2 v (k+p) U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v (k+p) U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v (k+p) U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v (k+p) U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n (k+p) U hU V T f hImage.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation S := (@CurrentPushforward.value R h2 v n (k+p) U V hU hV T f hImage hf hp).
Let hS:=@current_pushforward_representable R h2 v n (k+p) U V hU hV T hT f hImage hf hp.
Local Notation rho := (@NormalisedCurrent.measure R h2 n (k+p) V hV S hS).
Local Notation etaS := (@NormalisedCurrent.auxiliary_density R h2 n (k+p) V hV S hS).
Local Notation hRS := (@NormalisedCurrent.laws R h2 n (k+p) V hV S hS).
Let hRho:=distribution_representation_measure (normalised_distribution_representation_laws hRS).
Let hRhoRadon:=distribution_representation_radon (normalised_distribution_representation_laws hRS).
Local Notation delta := (@current_image_density R v n (k+p) U f xi).
Local Notation H := (real_total_integrand (fun x=>DN (delta x))).
Local Notation lambda := (measure_with_density mu H).
Local Notation nu := (@current_pushforward_weight R h2 v n (k+p) U V hU f hImage T hT).
Let hn:=@current_pushforward_weight_measure R h2 v n (k+p) U V hU f hImage T hT.
Let hrn:=@current_pushforward_weight_radon R h2 v n (k+p) U V hU hV f hImage hf T hT hp.
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 v n d U V hU hV f hImage hf).
Variable psi:Y->A_m Y R^o k.
Variable M:R.
Hypothesis hPsi:@is_baire_function R VT (real_norm_metric_space (@current_form_comass_real_norm R h2 n k))
  (fun y:VT=>(psi (set_val y):real_norm_metric_space (@current_form_comass_real_norm R h2 n k))).
Hypothesis hM:0<=M.
Hypothesis hBound:forall y,V y->@current_form_comass R h2 n k (psi y)<=M.
Arguments hBound : clear implicits.
Local Notation sourceField := (@current_form_pullback_on_domain R v n k U V f psi).
Local Notation targetField := (fun y:VT=>psi (set_val y)).
Let hSourceField:=@current_baire_form_pullback_locally_summable R h2 v n k U V hU hV f hImage hf
  mu hm hr psi M hPsi hM hBound.
Let hTargetField:=@bounded_baire_field_locally_summable R VT (A_m Y R^o k)
  (@current_form_comass R h2 n k) (@current_form_comass_real_norm R h2 n k)
  rho hRho hRhoRadon targetField M hPsi hM (fun y=>hBound (set_val y) (set_valP y)).

(** Source for [current_baire_source_contraction]: the
    actual T contracted with f#psi in
    the bounded Baire projection of Federer
    4.1.7, p. 359. Its local summability
    has just been proved from the original inputs. *)
Definition current_baire_source_contraction:@current_space R h2 v U hU p:=
  @current_measurable_contraction R h2 v k p U hU T hT sourceField hSourceField.

(** Source for [current_baire_target_contraction]: the
    actual f#T contracted with psi in
    Federer 4.1.7, p. 359. The
    original variation measure of f#T is
    used by the actual contraction constructor. *)
Definition current_baire_target_contraction:@current_space R h2 n V hV p:=
  @current_measurable_contraction R h2 n k p V hV S hS targetField hTargetField.
Local Notation C := current_baire_source_contraction.
Local Notation B := current_baire_target_contraction.

(** Source for [current_baire_source_contraction_support]:
    the actual Baire contraction has support
    in spt T, supporting properness of
    its pushforward in Federer 4.1.7,
    p. 359. This follows from the
    original integral action, not continuity of psi. *)
Theorem current_baire_source_contraction_support:
  @current_support R h2 v U hU p C `<=` @current_support R h2 v U hU (k+p) T.
Proof.
exact:(@current_measurable_multiplier_support_subset R h2 v (k+p) p U hU
  (A_m X R^o k) (@current_form_comass R h2 v k) (@current_form_comass_real_norm R h2 v k)
  (@current_form_separable R h2 v k) (@current_density_form_contraction R h2 v k p)
  (@current_density_form_contraction_bounded R h2 v k p) T hT sourceField hSourceField).
Qed.

(** Source for [current_baire_source_contraction_proper]:
    original support-properness of f suffices
    for the actual source Baire contraction,
    supporting Federer 4.1.7, p. 359. *)
Theorem current_baire_source_contraction_proper:
  @is_current_proper_on_support R h2 v n p U hU V C f hImage.
Proof.
exact:(@current_proper_smaller_support R h2 v n U hU V f hImage (k+p) p T C
  current_baire_source_contraction_support hp).
Qed.
Local Notation hCProper := current_baire_source_contraction_proper.

(** Source for [current_pushforward_baire_projection]:
    f#(T contracted with f#psi) equals
    f#T contracted with psi for every
    original bounded Baire k-form, Federer
    4.1.7, p. 359. The integration-representable
    statement proved here includes the printed
    locally normal and normal cases. No
    global source properness or finite total
    variation is added. *)
Theorem current_pushforward_baire_projection:
  @CurrentPushforward.value R h2 v n p U V hU hV C f hImage hf hCProper=B.
Proof.
have [u [z hData]]:=@current_pushforward_weighted_lone_pairing R h2 v n (k+p) U V hU hV
  T hT f hImage hf hp hS.
have [hUM [hUL [hUnit [hReconstruct [hZ [hZUnit [hZAction [hZFields hPairs]]]]]]]]:=hData.
apply:(@current_values_extensional R h2 n p V hV)=>phi.
have [K hK]:=smooth_test_support_bound (hE p) phi.
have [Q [hQC [W [hW [hTW [hWU hAgreement]]]]]]:=
  @current_proper_pullback_tests R h2 v n p (k+p) U V hU hV T f hImage hf hp K.
pose alpha:=Q (smooth_test_inclusion (hE p) phi).
have hAlpha x (hx:W x):@current_test_value R h2 v U hU p alpha x=
    fv p (pull p (smooth_test_inclusion (hE p) phi)) x.
  exact:(@hAgreement (smooth_test_inclusion (hE p) phi) hK x hx).
have hReplacement:@is_current_pullback_test_replacement R h2 v n p U V hU hV C f hImage hf phi alpha.
  exists W;split;first exact:hW.
  split;first by move=>x hx;exact:(@hTW x (@current_baire_source_contraction_support x hx)).
  split;[exact:hWU|exact:hAlpha].
have hPushValue:=@CurrentPushforward.laws R h2 v n p U V hU hV C f hImage hf hCProper phi alpha hReplacement.
pose theta:=fun y:VT=>form_wedge h2 (scalar_bilinear R) (psi (set_val y)) (ev p phi (set_val y)).
have hTheta:=@current_baire_test_product_lone R h2 n k p V hV nu hn hrn targetField M
  hPsi hM (fun y=>hBound (set_val y) (set_valP y)) phi.
have hThetaMeas:is_measure_measurable_function nu
    (partial_function_total (fun y=>(theta y:real_norm_metric_space hAN))).
  exact:hTheta.2.1.1.
have [a [hSourceWeighted hTargetWeighted]]:=@hPairs
  (partial_function_total (fun y=>(theta y:real_norm_metric_space hAN))) hTheta.
have hTargetReal:=measure_integral_graph_equivalent
  (@abstract_dual_partial_pairing_total_graph R VT A D ed z theta) hTargetWeighted.
have hSourceMeas:=@current_baire_test_source_measurable R h2 v n k p U V hV f hImage hf
  mu hm hr psi hPsi phi.
pose sourceTheta:=fun x:UT=>(theta (fU x):real_norm_metric_space hAN).
have hSourcePair:is_measure_integral lambda
    (abstract_dual_partial_pairing ed u (partial_function_total sourceTheta)) a%:E.
  apply:(@measure_integral_graph_equivalent R UT lambda _ _ _ _ hSourceWeighted)=>x t.
  rewrite !abstract_dual_partial_pairing_graph;by [].
have hWeightMeas:=@current_image_weight_measurable R h2 v n (k+p) U V hU hV f hImage hf
  mu hm hr xi (normalised_distribution_density_unit_bound hRepresentation)
  (distribution_representation_weak_measurable hBase).
have hPositive:=@current_image_weight_nonnegative R h2 v n (k+p) U f mu hm xi.
have hRaw:=(@weighted_dual_total_pairing_integral R UT A AN hAN
  (@current_form_separable R h2 n (k+p)) D ed DN hDual O hO mu lambda hm
  (fun x=>DN (delta x)) delta u sourceTheta (measure_with_density_laws mu H)
  hWeightMeas hPositive hUM hUnit hReconstruct hSourceMeas a%:E).1 hSourcePair.
have hOriginal:=@current_measurable_contraction_action R h2 v k p U hU T hT sourceField hSourceField alpha.
have hCarried:measure_almost_everywhere mu
    [set x:UT|@current_support R h2 v U hU (k+p) T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 v (k+p) U hU T hT).
have hAlmost:measure_almost_equal mu
    (real_total_integrand (fun x=>ed (delta x) (sourceTheta x)))
    (real_total_integrand (fun x=>pairing (xi x) (form_wedge h2 (scalar_bilinear R)
      (sourceField x) (@current_test_value R h2 v U hU p alpha (set_val x))))).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hCarried)=>x hx.
  have hPair:=@current_baire_projection_pairing R h2 v n k p U V hU hV f hImage hf
    xi psi (smooth_test_inclusion (hE p) phi) x.
  have hAt:=@hAlpha (set_val x) (@hTW (set_val x) hx).
  change (pairing (delta x) (theta (fU x))=pairing (xi x)
    (form_wedge h2 (scalar_bilinear R) (sourceField x)
      (fv p (pull p (smooth_test_inclusion (hE p) phi)) (set_val x)))) in hPair.
  rewrite -hAt in hPair.
  exists (ed (delta x) (sourceTheta x))%:E;split;rewrite real_total_integrand_graph;first by [].
  by rewrite MultivectorDual.laws hPair.
have hRawOriginal:=measure_integral_almost_equal hm hRaw hAlmost.
have hSourceValue:@current_value R h2 v U hU p C alpha=a.
  exact:(EFin_inj (measure_integral_unique hOriginal hRawOriginal)).
have hTargetOriginal:=@current_measurable_contraction_action R h2 n k p V hV S hS
  targetField hTargetField phi.
have hTargetValues:(fun y:VT=>pairing (etaS y)
    (form_wedge h2 (scalar_bilinear R) (targetField y) (ev p phi (set_val y))))=
    (fun y=>ed (etaS y) (theta y)).
  by apply:funext=>y;rewrite MultivectorDual.laws.
rewrite hTargetValues in hTargetOriginal.
have hTargetNu:=(@hZFields theta hThetaMeas (@current_value R h2 n V hV p B phi)%:E).1 hTargetOriginal.
have hTargetValue:a=@current_value R h2 n V hV p B phi.
  exact:(EFin_inj (measure_integral_unique hTargetReal hTargetNu)).
exact:(eq_trans hPushValue (eq_trans hSourceValue hTargetValue)).
Qed.
End CurrentPushforwardBaireProjection.
