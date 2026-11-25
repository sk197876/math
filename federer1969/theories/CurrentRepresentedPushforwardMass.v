(** Federer (1969), 4.1.11, p. 365: the exact
    exterior-image mass bound under any given Radon
    representation. This is the preceding pushforward
    inequality of 4.1.7, p. 359, after the original
    density-variation formula, without a normalization
    hypothesis on the given density or finite total mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorMaps CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed OpenCurrentDensityUP
  CurrentRepresentedDensityVariation CurrentRepresentedUnitDensity CurrentDensityNormMeasurable
  CurrentNormDensityRadon CurrentImageDensityPairing CurrentImageWeightRadon
  CurrentProperSupport CurrentProperSupportDomain CurrentPushforwardSealed CurrentMassSealed
  CurrentPushforwardMassIntegral DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP OpenFamilyTopologyMathcomp
  PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureDensity RealFiniteDensityIntegral MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralAlmostEquality MeasurableFunctionUP RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRepresentedPushforwardMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y.
Local Notation UT := (current_domain R v U).
Local Notation VN := (@current_vector_mass R h2 v m).
Local Notation WN := (@current_vector_mass R h2 n m).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->exterior_power X m.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 v m U gamma xi.
Variable T:@current_space R h2 v U hU m.
Hypothesis hRep:@is_current_integration_representation R h2 v m U hU T gamma xi.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation theta := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).
Local Notation Image := (@current_image_density R v n m U f).
Local Notation push := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).

(** Source for [current_represented_pushforward_mass_bound]:
    M(f#T) is bounded by the integral of the mass of
    Lambda_m Df(x)(xi(x)) under the original representing
    measure gamma. This is the exact weight used in
    Federer 4.1.11, p. 365, through 4.1.7, pp. 358–359.
    Every original integral value, including infinity, is retained. *)
Theorem current_represented_pushforward_mass_bound a:
  is_measure_integral gamma (real_total_integrand (fun x=>WN (Image xi x))) a->
  (@CurrentMass.value R h2 n m V hV push<=a)%E.
Proof.
move=>hIntegral.
have [w [hW [hWL [hUnit [hReconstruct hAgree]]]]]:=
  @current_represented_unit_density R h2 v m U hU gamma hGamma hRadon xi hField T hRep hT.
have hPositive:=@current_mass_density_nonnegative R h2 v m U gamma hGamma xi.
have hNormMeas:=@current_density_mass_measurable R h2 v m UT gamma hGamma xi hField.1.
have hLambda:=@measure_with_density_is_measure R UT gamma hGamma H hPositive.
have hWeight:=@current_image_weight_measurable R h2 v n m U V hU hV f hImage hf
  gamma hGamma hRadon w hUnit hW.
have hPoint:(fun x=>WN (Image w x)*VN (xi x))=(fun x=>WN (Image xi x)).
  apply:funext=>x.
  have hImageScale:Image xi x=VN (xi x)*:Image w x.
    by rewrite /current_image_density -{1}(hReconstruct x) linearZ.
  rewrite hImageScale (real_seminorm_scale (@current_vector_mass_real_norm R h2 n m).1)
    (ger0_norm (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 v m).1 (xi x))).
  exact:mulrC.
have hProduct:is_measure_integral gamma
    (real_total_integrand (fun x=>WN (Image w x)*VN (xi x))) a by rewrite hPoint.
have hWIntegral:=(@real_finite_density_integral_iff R UT gamma lambda hGamma
  (fun x=>VN (xi x)) (fun x=>WN (Image w x)) (measure_with_density_laws gamma H)
  hNormMeas hPositive hWeight a).2 hProduct.
have hThetaIntegral:is_measure_integral lambda (real_total_integrand (fun x=>WN (Image theta x))) a.
  apply:(measure_integral_almost_equal hLambda hWIntegral).
  apply:(@measure_almost_everywhere_mono R UT lambda hLambda _ _ _ hAgree)=>x hx.
  exists (WN (Image w x))%:E;split;first by rewrite real_total_integrand_graph.
  by rewrite real_total_integrand_graph /current_image_density hx.
have hVariation:=@current_represented_original_variation R h2 v m U hU
  gamma hGamma hRadon xi hField T hRep hT.
have hCanonical:=@current_pushforward_mass_weight_integral R h2 v n m U V hU hV T hT
  f hImage hf.
have hBound:=@current_pushforward_mass_integral_bound R h2 v n m U V hU hV T hT
  f hImage hf hp.
rewrite hVariation in hCanonical hBound.
have hValue:=measure_integral_unique hCanonical hThetaIntegral.
by rewrite hValue in hBound.
Qed.
End CurrentRepresentedPushforwardMass.
