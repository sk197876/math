(** Federer (1969), 4.1.7, p. 358:
    the original variation of gamma wedge xi
    is gamma restricted by mass(xi). The
    proof follows the printed scalar domination,
    bounded-density and multivector uniqueness route.
    Every measure remains on the original open U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RadonMeasureUP RealMetricBackground Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed CurrentIntegrationCriterion
  NormalisedCurrentSealed OpenCurrentDensityUP OpenCurrentDensitySealed CurrentNormDensityRadon
  CurrentDensityNormalisedAction CurrentDensityVariationBoundedDensity CurrentBoundedDensityTransfer
  BoundedCurrentDensityUniqueness OpenFamilyTopologyMathcomp PartialFunctionBasic SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasureStepIntegralIdentification TotalScalarMeasurability MeasureDensity MeasureDensityTransfer
  RealFiniteDensityIntegral BorelRegularMeasureUP RadonBorelRegularity
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDensityVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Local Notation T := (@OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon xi hField).
Local Notation S := (@current_value R h2 n U hU m T).
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).

(** Source for [current_density_exact_variation]:
    ||gamma wedge xi||=gamma restricted by
    mass(xi), Federer 4.1.7, p. 358,
    first displayed formula. The original scalar-test
    variation measure is retained on every set.
    Radon gamma and the printed local integrability
    of xi are the only analytic inputs. *)
Theorem current_density_exact_variation (nu:set UT->\bar R) (eta:UT->V):
  @is_normalised_current_representation R h2 n m U hU T nu eta ->nu=lambda.
Proof.
move=>hRepresentation.
have hPositive:=@current_mass_density_nonnegative R h2 n m U gamma hGamma xi.
have hLambda:is_measure lambda:=measure_with_density_is_measure hGamma hPositive.
have hLambdaRadon:=@current_mass_density_radon R h2 n m U hU gamma hGamma hRadon xi hField.
have [w [hW [hWBound [hWUnit hWAction]]]]:=
  @current_mass_density_unit_representation R h2 n m U hU gamma hGamma hRadon xi hField.
have [k [hRange [hK hDensity]]]:=@current_variation_original_bounded_density R h2 n m U hU
  gamma hGamma hRadon xi hField nu eta hRepresentation.
have hKReal:=@total_scalar_real_measurable R UT lambda hLambda k hK.1.
have hKMeas:=@measurable_partial_real_embedding R UT lambda hLambda
  (partial_function_total (k:UT->real_line_metric R)) hKReal.
have hBase:=normalised_distribution_representation_laws hRepresentation.
have hNu:=distribution_representation_measure hBase.
have hNuRadon:=distribution_representation_radon hBase.
have [z [hZ [hZBound [hZMass hZAction]]]]:=
  @current_bounded_density_transfer R h2 n m U hU lambda nu hLambda hNu hLambdaRadon hNuRadon
    k hKMeas hRange hDensity eta (distribution_representation_weak_measurable hBase)
    (normalised_distribution_density_unit_bound hRepresentation)
    (normalised_distribution_density_unit_norm hRepresentation) S
    (distribution_representation_action hBase).
have hUnique:=@bounded_current_density_almost_unique R h2 n m U hU lambda hLambda hLambdaRadon
  w z hW hZ hWBound hZBound S hWAction hZAction.
have hKOne:measure_almost_everywhere lambda [set x|k x = 1].
  apply:(@measure_almost_everywhere_mono R UT lambda hLambda _ _ _
    (measure_almost_everywhere_and hLambda
      (measure_almost_everywhere_and hLambda hWUnit hZMass) hUnique))=>x [[hOne hMass] hEq].
  exact:(eq_trans (esym hMass) (eq_trans (congr1 VN (esym hEq)) hOne)).
have hEqual:measure_almost_equal lambda (real_total_integrand k) (real_total_integrand (fun _=>1)).
  apply:(@measure_almost_everywhere_mono R UT lambda hLambda _ _ _ hKOne)=>x hx.
  exists (1:R)%:E; split; by rewrite real_total_integrand_graph ?hx.
have hUnitDensity:=@measure_density_almost_equal R UT lambda nu hLambda
  (real_total_integrand k) (real_total_integrand (fun _=>1)) hDensity hEqual.
have hRegular:=borel_regular_is_regular hLambda (radon_borel_regular hLambda hLambdaRadon).
have hValue:=@regular_measure_unit_density_value R UT lambda nu hLambda hRegular hUnitDensity.
apply:funext=>A; exact:hValue A.
Qed.

(** Source for [current_open_density_representable]:
    the original gamma wedge xi is representable
    by integration, Federer 4.1.7, pp. 356–358.
    Its given gamma and xi are the witnesses. *)
Lemma current_open_density_representable:
  @is_integration_representable_current R h2 n m U hU T.
Proof.
exists gamma,xi; exact:OpenCurrentDensity.laws.
Qed.

(** Source for [current_open_density_variation]: the
    opaque original variation measure of the
    actual density current is exactly gamma
    restricted by mass(xi), Federer 4.1.7,
    p. 358. The proof argument merely indexes
    the original representable-current interface. *)
Theorem current_open_density_variation
    (hT:@is_integration_representable_current R h2 n m U hU T):
  @NormalisedCurrent.measure R h2 n m U hU T hT=lambda.
Proof.
exact:(current_density_exact_variation (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Qed.
End CurrentDensityVariation.
