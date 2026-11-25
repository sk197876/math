(** Federer (1969), 4.1.7, p. 359:
    the normalized exterior image evaluates every
    original pushed test under the exact
    weighted source measure. The earlier source
    integral formula and 2.4.10, p. 85,
    prove this before extending to Baire fields. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentIntegrationCriterion
  CurrentMultivectorDual MultivectorDualSealed NormalisedCurrentSealed CurrentProperSupport CurrentProperSupportDomain
  CurrentImageDensityPairing CurrentImageWeightRadon CurrentPushforwardSealed CurrentPushforwardIntegralAction
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP CompactContinuousVectorFields
  AbstractDualPartialPairing WeightedDualTotalPairing OpenFamilyTopologyMathcomp
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition MeasureUP MeasureDensity
  MeasureIntegralUP MeasureIntegralGraphEquivalence RadonMeasureUP MeasurableFunctionUP
  MeasurableIdentityCriterion MeasurableTotalBasic BorelFunctionBasic SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardWeightedTestAction.
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

(** Source for [current_pushforward_weighted_test_action]:
    normalization changes the source measure but
    preserves the actual pushed test action,
    supporting the Baire projection in Federer
    4.1.7, p. 359. The normalized
    witness is specified by pointwise reconstruction;
    no target representation is assumed. *)
Theorem current_pushforward_weighted_test_action (u:UT->D):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(u x:open_family_topological_space hO.1)))->
  (forall x,DN (u x)<=1)->(forall x,DN (delta x)*:u x=delta x)->
  forall phi:DT,is_measure_integral lambda
    (abstract_dual_partial_pairing ed u
      (partial_function_precompose fU (partial_function_total
        (fun y:VT=>(dvalues phi y:real_norm_metric_space hAN)))))
    (@current_value R h2 n V hV m S phi)%:E.
Proof.
move=>hMeasU hUnit hReconstruct phi.
have hF:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
have hPhi:=@smooth_test_original_continuous_field R Y A NY AN hNY hAN V
  (@current_smooth_space R h2 n V hV m) (@current_smooth_value R h2 n V hV m) hE phi.
pose eta:=fun x:UT=>(dvalues phi (fU x):real_norm_metric_space hAN).
have hContinuous:continuous eta.
  move=>x;exact:(continuous_comp (hF x) (hPhi.1 (fU x))).
have hIdentity:=(@measurable_identity_iff_open_sets R UT mu hm).2 (radon_open_measurable hr).
have hEta:=@measurable_total_borel_postcomposition R UT UT (real_norm_metric_space hAN)
  mu hm id eta hIdentity (continuous_borel_function hContinuous).
have hSource:=@current_pushforward_original_integral_action R h2 v n m U V hU hV
  T hT f hImage hf hp phi.
have hValues:(fun x:UT=>pairing (delta x) (@current_test_value R h2 n V hV m phi (f (set_val x))))=
    (fun x=>ed (delta x) (eta x)).
  by apply:funext=>x;rewrite MultivectorDual.laws.
rewrite hValues in hSource.
have hWeightMeas:=@current_image_weight_measurable R h2 v n m U V hU hV f hImage hf
  mu hm hr xi (normalised_distribution_density_unit_bound hRepresentation)
  (distribution_representation_weak_measurable hBase).
have hWeightPositive:=@current_image_weight_nonnegative R h2 v n m U f mu hm xi.
have hIntegral:=(@weighted_dual_total_pairing_integral R UT A AN hAN
  (@current_form_separable R h2 n m) D ed DN hDual O hO mu lambda hm
  (fun x=>DN (delta x)) delta u eta (measure_with_density_laws mu H)
  hWeightMeas hWeightPositive hMeasU hUnit hReconstruct hEta _).2 hSource.
apply:(@measure_integral_graph_equivalent R UT lambda _ _ _ _ hIntegral)=>x z.
rewrite !abstract_dual_partial_pairing_graph.
by [].
Qed.
End CurrentPushforwardWeightedTestAction.
