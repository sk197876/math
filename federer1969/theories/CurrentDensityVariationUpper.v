(** Federer (1969), 4.1.7, p. 358: the
    original variation of gamma wedge xi is
    bounded by gamma restricted by mass(xi).
    This first step uses the original scalar-test
    gauge and the actual mass/comass pairing bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import BorelRegularMeasureUP PartialExtendedOrderLoci RadonBorelRegularity RadonMeasureUP Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  RealFunctionalNormUP ContinuousDualUP CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed MultivectorDualUP OpenCurrentDensityUP OpenCurrentDensitySealed
  CurrentIntegrationCriterion CurrentDensityNormMeasurable CurrentNormDensityRadon
  RadonCompactScalarIntegral RealFiniteDensityIntegral FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportSummability SummableRealFunctionUP RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureDensity MeasureIntegralUP
  MeasureIntegralUniqueness MeasureIntegralComparison DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP DistributionVariationUP DistributionVariationBasic
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDensityVariationUpper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable gamma:set UT->\bar R.
Hypothesis hGammaInput:is_measure gamma.
Hypothesis hRadonInput:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Local Notation T := (@OpenCurrentDensity.value R h2 n m U hU gamma hGammaInput hRadonInput xi hField).
Local Notation action := (@current_value R h2 n U hU m T).
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).
Local Notation hGamma := hGammaInput.
Local Notation hRadonGamma := hRadonInput.
Local Notation hLambda := (measure_with_density_is_measure hGamma
  (@current_mass_density_nonnegative R h2 n m U gamma hGammaInput xi)).
Local Notation hRadonLambda := (@current_mass_density_radon R h2 n m U hU gamma hGammaInput hRadonInput xi hField).
Local Notation F := (@radon_positive_compact_integral R UT lambda hLambda hRadonLambda).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R UT)).

(** Source for [current_density_original_gauge_upper]:
    every original scalar-test variation is at
    most the literal mass-density integral, supporting
    Federer 4.1.7, p. 358. The multivector
    density need not be normalized or bounded. *)
Theorem current_density_original_gauge_upper f c:
  Kplus f ->is_distribution_variation_value NY dvalues action f c ->(c<=(F f)%:E)%E.
Proof.
move=>hf hGauge.
have hF:=@radon_positive_compact_integral_laws R UT lambda hLambda hRadonLambda f hf.
have hH:=@current_density_mass_measurable R h2 n m UT gamma hGamma xi
  hField.1.
have hFMeas:=@continuous_real_integrand_measurable R UT gamma hGamma
  (fun B hB=>borel_regular_borel_measurable hGamma (radon_borel_regular hGamma hRadonGamma) hB)
  f hf.1.1.
have hProduct:=(@real_finite_density_integral_iff R UT gamma lambda hGamma
  (fun x=>VN (xi x)) f (measure_with_density_laws gamma H) hH
  (@current_mass_density_nonnegative R h2 n m U gamma hGammaInput xi) hFMeas (F f)%:E).1 hF.
have hRepresentation:=@OpenCurrentDensity.laws R h2 n m U hU gamma hGammaInput hRadonInput xi hField.
apply:(@distribution_variation_least_finite_bound R UT Y NY DT dvalues action f c (F f)
  hGauge)=>psi hPsi.
have hOriginal:=distribution_representation_action hRepresentation psi.
have hPointwise x:ed (xi x) (dvalues psi x)<=f x*VN (xi x).
  have hBound:=real_functional_norm_bound (continuous_dual_norm_laws hDual (xi x)) (dvalues psi x).
  have hScale:=ler_wpM2l (real_functional_norm_nonnegative
    (continuous_dual_norm_laws hDual (xi x))) (hPsi x).
  rewrite mulrC; exact:le_trans (ler_norm _) (le_trans hBound hScale).
have hOrder:measure_almost_everywhere gamma
    (partial_extended_le_locus (real_total_integrand (fun x=>ed (xi x) (dvalues psi x)))
      (real_total_integrand (fun x=>f x*VN (xi x)))).
  apply:(@measure_almost_everywhere_mono R UT gamma hGamma setT _ _
    (measure_almost_everywhere_true hGamma))=>x _.
  exists (ed (xi x) (dvalues psi x))%:E,(f x*VN (xi x))%:E; split;
    first by rewrite real_total_integrand_graph.
  split; first by rewrite real_total_integrand_graph.
  rewrite lee_fin; exact:hPointwise.
have hBound:=@measure_integral_monotone R UT gamma hGamma _ _ _ _ hOriginal hProduct hOrder.
by move:hBound; rewrite lee_fin.
Qed.
End CurrentDensityVariationUpper.
