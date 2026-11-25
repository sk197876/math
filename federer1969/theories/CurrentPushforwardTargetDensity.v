(** Federer (1969), 4.1.7, p. 359:
    express the actual pushed current under
    the dominating weighted image measure.
    The original compact scalar gauge bound
    and the preceding bounded-density argument
    give an auxiliary unit-bounded density.
    This does not identify that measure with
    the smaller original variation of f#T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureIntegralUP Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates ExteriorGrading AlternatingForms
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed CurrentIntegrationCriterion NormalisedCurrentSealed CurrentProperSupport
  CurrentPushforwardSealed CurrentPushforwardWeight CurrentPushforwardVariation CurrentBoundedDensityTransfer
  SmoothDomainCompactOpenCover SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain
  DistributionVariationBasic DistributionIntegralFieldUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge
  RadonOrderedCompactDensity RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP
  OpenFamilyTopologyMathcomp MetricSubsetBackground RealMetricBackground PartialFunctionBasic
  MeasurableFunctionUP MeasureStepIntegralIdentification TotalScalarMeasurability SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardTargetDensity.
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
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:NormRegularity.norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation action := (@current_value R h2 n V hV m S).
Local Notation nu := (@current_pushforward_weight R h2 v n m U V hU f hImage T hT).
Let hn:=@current_pushforward_weight_measure R h2 v n m U V hU f hImage T hT.
Let hrn:=@current_pushforward_weight_radon R h2 v n m U V hU hV f hImage hf T hT hp.
Local Notation F := (@radon_positive_compact_integral R VT nu hn hrn).

(** Source for [current_pushforward_weight_unit_representation_full]:
    the actual f#T has a unit-bounded
    weak density under its original dominating
    weighted image measure, supporting Baire
    projection in Federer 4.1.7, p. 359.
    Scalar domination and representation are proved
    beforehand for the actual pushed current. *)
Theorem current_pushforward_weight_unit_representation_full
    (hPush:@is_integration_representable_current R h2 n m V hV S):
  exists z:VT->D,
    is_measure_measurable_function nu
      (partial_function_total (fun y=>(z y:open_family_topological_space hO.1))) /\
    (forall y,DN (z y)<=1) /\is_distribution_integral_action nu ed z dvalues action /\
    forall g:VT->real_norm_metric_space hAN,
      is_measure_measurable_function nu (partial_function_total g)->forall a,
      is_measure_integral (@NormalisedCurrent.measure R h2 n m V hV S hPush)
        (real_total_integrand (fun y=>ed
          (@NormalisedCurrent.auxiliary_density R h2 n m V hV S hPush y) (g y))) a<->
      is_measure_integral nu (real_total_integrand (fun y=>ed (z y) (g y))) a.
Proof.
pose rho:=@NormalisedCurrent.measure R h2 n m V hV S hPush.
pose eta:=@NormalisedCurrent.auxiliary_density R h2 n m V hV S hPush.
have hR:=@NormalisedCurrent.laws R h2 n m V hV S hPush.
have hBase:=normalised_distribution_representation_laws hR.
have hm:=distribution_representation_measure hBase.
have hr:=distribution_representation_radon hBase.
pose G:=@normalised_distribution_scalar_integral R VT A AN hAN D ed DN hDual O hO
  DT dvalues action rho eta hR.
have hG:=@normalised_distribution_scalar_integral_laws R VT A AN hAN D ed DN hDual O hO
  DT dvalues action rho eta hR.
have hF:=@radon_positive_compact_integral_laws R VT nu hn hrn.
have hOrder g (hg:positive_function_lattice (@compactly_supported_continuous_functions R VT) g):G g<=F g.
  have hGauge:=@normalised_scalar_integral_original_gauge R VT A AN hAN D ed DN hDual O hO
    DT dvalues action rho eta hR g hg.
  have hBound:=@distribution_variation_least_finite_bound R VT A AN DT dvalues action g (G g)%:E (F g)
    hGauge (@current_pushforward_compact_test_bound R h2 v n m U V hU hV T hT f hImage hf hp g hg).
  by rewrite lee_fin in hBound.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R Y NY hNY n (@coordinate_basis R n) (@coordinate_basisP R n) V hV.
have [k [hRange [hLattice hDensity]]]:=@radon_ordered_compact_measure_density R
  (metric_subset (V:set (real_norm_metric_space hNY))) nu rho hn hm hrn hr F G C W
  hF hG hOrder hC hW hWC hCover hWCover.
have hKReal:=@total_scalar_real_measurable R VT nu hn k hLattice.1.
have hKMeas:=@measurable_partial_real_embedding R VT nu hn
  (partial_function_total (fun y=>(k y:real_line_metric R))) hKReal.
have [z [hZ [hBound [hMass [hAction hFields]]]]]:=@current_bounded_density_transfer_full R h2 n m V hV nu rho hn hm hrn hr
  k hKMeas hRange hDensity eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hR) (normalised_distribution_density_unit_norm hR)
  action (distribution_representation_action hBase).
exists z;split;first exact:hZ.
split;first exact:hBound.
split;[exact:hAction|exact:hFields].
Qed.

(** Source for [current_pushforward_weight_unit_representation]:
    the actual pushed current has a
    unit-bounded density under its original
    dominating weighted image measure, supporting
    Federer 4.1.7, p. 359. The
    preceding stronger theorem also retains
    every measurable scalar pairing integral. *)
Theorem current_pushforward_weight_unit_representation
    (hPush:@is_integration_representable_current R h2 n m V hV S):
  exists z:VT->D,
    is_measure_measurable_function nu
      (partial_function_total (fun y=>(z y:open_family_topological_space hO.1))) /\
    (forall y,DN (z y)<=1) /\is_distribution_integral_action nu ed z dvalues action.
Proof.
have [z [hZ [hBound [hAction hFields]]]]:=current_pushforward_weight_unit_representation_full hPush.
exists z;split;first exact:hZ.
split;[exact:hBound|exact:hAction].
Qed.
End CurrentPushforwardTargetDensity.
