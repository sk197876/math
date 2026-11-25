(** Federer (1969), 4.1.7, p. 358:
    applying the earlier dominated-Daniell theorem
    to the original variation and mass-density
    integrals. This stage gives a scalar density
    bounded by one; its positivity and the exact
    measure equality are separate assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionLattice FiniteCoordinates FunctionLatticeLaws SummableRealFunctionUP Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms MetricSubsetBackground CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  OpenCurrentDensityUP OpenCurrentDensitySealed CurrentIntegrationCriterion
  CurrentNormDensityRadon CurrentDensityVariationUpper RadonCompactScalarIntegral
  FunctionLatticeUP CompactSupportFunctionUP MeasureUP MeasureDensity RadonMeasureUP
  RealIntegralFunctionalUP RealIntegralFunctional RealLatticeDensityUP RadonDominatedCompactDensity
  RadonBoundedPositiveDensity SmoothDomainCompactOpenCover RadonCompactCoverCountablyMeasurable
  RadonBoundedDensityIdentification MeasureDensityUP
  NormalisedDistributionRepresentationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge DistributionVariationBasic
  DaniellIntegralNegation SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDensityVariationBoundedDensity.
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
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
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
Local Notation hLambda := (measure_with_density_is_measure hGammaInput
  (@current_mass_density_nonnegative R h2 n m U gamma hGammaInput xi)).
Local Notation hRadonLambda := (@current_mass_density_radon R h2 n m U hU gamma hGammaInput hRadonInput xi hField).
Local Notation F := (@radon_positive_compact_integral R UT lambda hLambda hRadonLambda).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R UT)).
Variable nu:set UT->\bar R.
Variable eta:UT->V.
Hypothesis hRepresentation:@is_normalised_current_representation R h2 n m U hU T nu eta.
Local Notation A := (@normalised_distribution_scalar_integral R UT Y NY hNY V ed VN hDual O hO
  DT dvalues action nu eta hRepresentation).

(** Source for [current_variation_compact_density_bounded]:
    the bounded density supplied by 2.5.9,
    p. 100, in Federer's proof of 4.1.7,
    p. 358. Here the domination is proved for
    the actual original gauge. No normalized-input
    density or separate domination assumption is added. *)
Theorem current_variation_compact_density_bounded:
  exists k:UT->R,is_real_lattice_density lambda Kplus A k /\forall x,`|k x|<=1.
Proof.
have hBase:=normalised_distribution_representation_laws hRepresentation.
have hNu:=distribution_representation_measure hBase.
have hA:=@normalised_distribution_scalar_integral_laws R UT Y NY hNY V ed VN hDual O hO
  DT dvalues action nu eta hRepresentation.
have hAlattice:=positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R UT).
have hAmonotone:=@real_integral_functional_is_monotone_daniell R UT nu hNu Kplus A hAlattice hA.
have hF:=@radon_positive_compact_integral_laws R UT lambda hLambda hRadonLambda.
have hFmonotone:=@radon_positive_compact_integral_daniell R UT lambda hLambda hRadonLambda.
have hBound f (hf:Kplus f):`|A f|<=F (fun x=>`|f x|).
  have hGauge:=@normalised_scalar_integral_original_gauge R UT Y NY hNY V ed VN hDual O hO
    DT dvalues action nu eta hRepresentation f hf.
  have hNonnegative:0<=A f.
    have h:=@distribution_variation_nonnegative R UT Y NY hNY DT dvalues action f (A f)%:E hf.2 hGauge.
    by move:h; rewrite lee_fin.
  have hUpper:=@current_density_original_gauge_upper R h2 n m U hU gamma hGammaInput hRadonInput xi hField
    f (A f)%:E hf hGauge.
  have hAbs:(fun x=>`|f x|)=f.
    apply:funext=>x; exact:ger0_norm (hf.2 x).
  rewrite hAbs (ger0_norm hNonnegative); by move:hUpper; rewrite lee_fin.
exact:(@radon_dominated_compact_density R UT lambda hLambda hRadonLambda F A
  hFmonotone hF (monotone_daniell_is_daniell hAmonotone) hBound).
Qed.

(** Source for [current_variation_positive_compact_density]:
    the bounded nonnegative scalar density in
    Federer's proof of 4.1.7, p. 358,
    through 2.5.9, p. 100. Its original
    compact scalar integrals are retained. The
    subsequent multivector identification is separate. *)
Theorem current_variation_positive_compact_density:
  exists k:UT->R,is_real_lattice_density lambda Kplus A k /\forall x,0<=k x<=1.
Proof.
have [k [hk hBound]]:=current_variation_compact_density_bounded.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
have hCount:=@radon_compact_cover_countably_measurable R UT lambda hLambda hRadonLambda C hC hCover.
have hPositive f (hf:Kplus f):0<=A f.
  have hGauge:=@normalised_scalar_integral_original_gauge R UT Y NY hNY V ed VN hDual O hO
    DT dvalues action nu eta hRepresentation f hf.
  have h:=@distribution_variation_nonnegative R UT Y NY hNY DT dvalues action f (A f)%:E hf.2 hGauge.
  by move:h; rewrite lee_fin.
exact:(@radon_bounded_positive_compact_density R UT lambda hLambda hRadonLambda A k
  hCount hk hPositive hBound).
Qed.

(** Source for [current_variation_original_bounded_density]:
    the original variation measure is the actual
    mass-density measure restricted by a bounded
    nonnegative scalar k, as in Federer's proof
    of 4.1.7, p. 358. Its final identification
    with the unweighted mass-density measure remains
    the subsequent multivector uniqueness step. *)
Theorem current_variation_original_bounded_density:
  exists k:UT->R,(forall x,0<=k x<=1) /\
    is_real_lattice_density lambda Kplus A k /\
    is_measure_density lambda (real_total_integrand k) nu.
Proof.
have [k [hk hRange]]:=current_variation_positive_compact_density.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
have hBase:=normalised_distribution_representation_laws hRepresentation.
have hA:=@normalised_distribution_scalar_integral_laws R UT Y NY hNY V ed VN hDual O hO
  DT dvalues action nu eta hRepresentation.
have hDensity:=@radon_bounded_compact_density_identifies_measure R (metric_subset (U:set XT))
  lambda nu hLambda (distribution_representation_measure hBase) hRadonLambda
  (distribution_representation_radon hBase) A k C W hA hk hRange hC hW hWC hCover hWCover.
exists k; split=>//; by split.
Qed.
End CurrentDensityVariationBoundedDensity.
