(** Federer (1969), 4.1.7, p. 359:
    the normalized exterior image and the
    actual pushed current have the same
    pairing on every original target L1 field.
    The preceding test action, actual test
    density of 4.1.5, p. 350, and
    uniqueness of the L1 extension prove this
    without assigning values outside partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates ExteriorGrading AlternatingForms
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentIntegrationCriterion
  CurrentMultivectorDual MultivectorDualSealed NormalisedCurrentSealed CurrentProperSupport CurrentProperSupportDomain
  CurrentImageDensityPairing CurrentImageDensityMeasurable CurrentImageWeightRadon CurrentDensityNormMeasurable
  CurrentWeightedUnitDensity CurrentPushforwardSealed CurrentPushforwardWeight CurrentPushforwardVariation
  CurrentPushforwardTargetDensity CurrentPushforwardWeightedTestAction SmoothDomainCompactOpenCover
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP DistributionIntegralFieldUP
  CompactContinuousVectorFields CompactContinuousVectorMeasurable SmoothTestLoneDensity RadonCompactScalarIntegral
  AbstractDualPartialPairing RadonImageUnitPairing DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralLipschitz
  LoneSeminormContinuityUP LoneLipschitzContinuity DenseLoneExtensionUniqueness OpenFamilyTopologyMathcomp
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition MeasureUP MeasureDensity MeasurePushforward
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence RadonMeasureUP
  RadonCompactCoverCountablyMeasurable MeasurableFunctionUP MeasureLpMembershipUP MeasureLpConvergence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardWeightedLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
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
Local Notation A := (A_m Y R^o m).
Local Notation AN := (@current_form_comass R h2 n m).
Local Notation hAN := (@current_form_comass_real_norm R h2 n m).
Local Notation D := (exterior_power Y m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R Y m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation DT := (@current_test_space R h2 n V hV m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNY) V A DT
  (smooth_test_values_hom hE)).
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation delta := (@current_image_density R v n m U f xi).
Local Notation H := (real_total_integrand (fun x=>DN (delta x))).
Local Notation lambda := (measure_with_density mu H).

Local Notation nu := (@current_pushforward_weight R h2 v n m U V hU f hImage T hT).
Let hn:=@current_pushforward_weight_measure R h2 v n m U V hU f hImage T hT.
Let hrn:=@current_pushforward_weight_radon R h2 v n m U V hU hV f hImage hf T hT hp.
Local Notation F := (@radon_positive_compact_integral R VT nu hn hrn).

(** Source for [current_pushforward_weighted_lone_pairing]:
    the original pushed action has its
    exact weighted-source integral on all target
    L1 fields, supporting the bounded Baire
    projection in Federer 4.1.7, p. 359.
    The two auxiliary unit-bounded densities are
    proved to exist under the original measures;
    no representation formula is assumed. *)
Theorem current_pushforward_weighted_lone_pairing
    (hPush:@is_integration_representable_current R h2 n m V hV S):
  exists u:UT->D,exists z:VT->D,
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(u x:open_family_topological_space hO.1))) /\
    is_measure_measurable_function lambda
      (partial_function_total (fun x=>(u x:open_family_topological_space hO.1))) /\
    (forall x,DN (u x)<=1) /\(forall x,DN (delta x)*:u x=delta x) /\
    is_measure_measurable_function nu
      (partial_function_total (fun y=>(z y:open_family_topological_space hO.1))) /\
    (forall y,DN (z y)<=1) /\
    is_distribution_integral_action nu ed z dvalues (@current_value R h2 n V hV m S) /\
    (forall g:VT->real_norm_metric_space hAN,
      is_measure_measurable_function nu (partial_function_total g)->forall a,
      is_measure_integral (@NormalisedCurrent.measure R h2 n m V hV S hPush)
        (real_total_integrand (fun y=>ed
          (@NormalisedCurrent.auxiliary_density R h2 n m V hV S hPush y) (g y))) a<->
      is_measure_integral nu (real_total_integrand (fun y=>ed (z y) (g y))) a) /\
    forall eta:partial_function VT (real_norm_metric_space hAN),
      is_measure_lp_function nu 1 eta->exists a:R,
      is_measure_integral lambda
        (abstract_dual_partial_pairing ed u (partial_function_precompose fU eta)) a%:E /\
      is_measure_integral nu (abstract_dual_partial_pairing ed z eta) a%:E.
Proof.
have hSep:=@current_form_separable R h2 n m.
have hDeltaNorm:=@current_image_density_measurable R h2 v n m U V hU hV f hImage hf
  xi (normalised_distribution_density_unit_bound hRepresentation) mu hm hr
  (distribution_representation_weak_measurable hBase).
have hDeltaWeak:=@current_density_weak_topology_measurable R h2 n m UT mu hm delta hDeltaNorm.
have [u [hUM [hUL [hUnit [hReconstruct hOne]]]]]:=
  @current_weighted_unit_density_exists R h2 n m UT mu hm delta hDeltaWeak.
have hPositive:=@current_image_weight_nonnegative R h2 v n m U f mu hm xi.
have hl:=@measure_with_density_is_measure R UT mu hm H hPositive.
have hrl:=@current_image_weight_radon R h2 v n m U V hU hV f hImage hf mu hm hr xi
  (normalised_distribution_density_unit_bound hRepresentation)
  (distribution_representation_weak_measurable hBase).
have hF:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
have [z [hZ [hZUnit [hZAction hZFields]]]]:=@current_pushforward_weight_unit_representation_full R h2 v n m U V hU hV
  T hT f hImage hf hp hPush.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R Y NY hNY n (@coordinate_basis R n) (@coordinate_basisP R n) V hV.
have hCount:=@radon_compact_cover_countably_measurable R VT nu hn hrn C hC hCover.
have [J [hJSource hJLipschitz]]:=@radon_image_unit_pairing_exists R UT VT A AN hAN hSep
  D ed DN hDual O hO lambda hl hrl fU hF hrn hCount u hUL hUnit.
pose I:=@DualLoneIntegral.value R VT A AN hAN hSep D ed DN hDual O hO nu hn z hZ hZUnit.
have hI:=@DualLoneIntegral.laws R VT A AN hAN hSep D ed DN hDual O hO nu hn z hZ hZUnit.
pose test:=fun phi:DT=>partial_function_total (fun y:VT=>(dvalues phi y:real_norm_metric_space hAN)).
have hTest phi:is_measure_lp_function nu 1 (test phi).
  exact:(@compact_continuous_vector_lone_member R VT A AN hAN hSep nu hn hrn F
    (@radon_positive_compact_integral_laws R VT nu hn hrn) (dvalues phi)
    (@smooth_test_original_continuous_field R Y A NY AN hNY hAN V
      (@current_smooth_space R h2 n V hV m) (@current_smooth_value R h2 n V hV m) hE phi)).
have hAgreement phi:I (test phi)=J (test phi).
  have hTarget:=hI (test phi) (hTest phi).
  have hTargetReal:=measure_integral_graph_equivalent
    (@abstract_dual_partial_pairing_total_graph R VT A D ed z (dvalues phi)) hTarget.
  have hIValue:I (test phi)=@current_value R h2 n V hV m S phi.
    exact:(congr1 (@fine R) (measure_integral_unique hTargetReal (hZAction phi))).
  have hSource:=hJSource (test phi) (hTest phi).
  have hOriginal:=@current_pushforward_weighted_test_action R h2 v n m U V hU hV
    T hT f hImage hf hp u hUM hUnit hReconstruct phi.
  have hJValue:J (test phi)=@current_value R h2 n V hV m S phi.
    exact:(congr1 (@fine R) (measure_integral_unique hSource hOriginal)).
  exact:(eq_trans hIValue (esym hJValue)).
have hILipschitz:=@dual_lone_integral_lipschitz R VT A AN hAN hSep D ed DN hDual O hO
  nu hn z hZ hZUnit I hI.
have hJContinuous:=@lone_lipschitz_seminorm_continuous R VT A AN hAN nu J hJLipschitz.
have hDense:=@smooth_test_lone_dense R n A AN hAN (@current_form_complete R h2 n m) hSep V hV
  (@current_smooth_space R h2 n V hV m) (@current_smooth_value R h2 n V hV m) hE
  nu hn hrn F (@radon_positive_compact_integral_laws R VT nu hn hrn).
have hEqual:=@dense_lone_extension_unique R VT A AN hAN nu hn DT test I J
  hILipschitz hJContinuous hDense hAgreement.
exists u,z;split;first exact:hUM.
split;first exact:hUL.
split;first exact:hUnit.
split;first exact:hReconstruct.
split;first exact:hZ.
split;first exact:hZUnit.
split;first exact:hZAction.
split;first exact:hZFields.
move=>eta hEta;exists (I eta);split;last exact:(hI eta hEta).
have hSource:=hJSource eta hEta.
by rewrite -(hEqual eta hEta) in hSource.
Qed.
End CurrentPushforwardWeightedLone.
