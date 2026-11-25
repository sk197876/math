(** Federer (1969), 4.1.11, p. 365: use the original
    density-variation identity before estimating the join.
    This adapter of 4.1.7, pp. 358–359, retains an arbitrary
    representing density and its pointwise reconstruction.
    No finite total mass or unit bound on that density is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed CurrentIntegrationCriterion NormalisedCurrentSealed OpenCurrentDensityUP
  CurrentWeightedUnitDensity CurrentUnitDensityTestIntegral CurrentNormDensityRadon
  CurrentDensityNormMeasurable CurrentRepresentedDensityVariation BoundedCurrentDensityUniqueness
  OpenFamilyTopologyMathcomp PartialFunctionBasic SummableRealFunctionUP MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureDensity MeasureDensityTransfer
  RealFiniteDensityIntegral MeasureIntegralUP SmoothFunctionSpaceUP SmoothTestEvaluation
  DistributionVariationDomain DistributionIntegralFieldUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRepresentedUnitDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y
  DT (smooth_test_values_hom hE)).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Variable T:@current_space R h2 n U hU m.
Hypothesis hRep:@is_current_integration_representation R h2 n m U hU T gamma xi.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).
Local Notation theta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).

(** Source for [current_represented_unit_density]: normalize
    the given density with respect to its exact mass-density
    measure and identify it with the original normalized
    current density almost everywhere. This supports the
    sharp join bound in Federer 4.1.11, p. 365, through
    the preceding representation and uniqueness of 4.1.7,
    pp. 358–359. Pointwise reconstruction is preserved. *)
Theorem current_represented_unit_density:
  exists w:UT->V,
    is_measure_measurable_function gamma
      (partial_function_total (fun x=>(w x:open_family_topological_space hO.1))) /\
    is_measure_measurable_function lambda
      (partial_function_total (fun x=>(w x:open_family_topological_space hO.1))) /\
    (forall x,VN (w x)<=1) /\
    (forall x,VN (xi x)*:w x=xi x) /\
    measure_almost_everywhere lambda [set x|w x=theta x].
Proof.
have [w [hW [hWL [hUnit [hReconstruct hOne]]]]]:=
  @current_weighted_unit_density_exists R h2 n m UT gamma hGamma xi hField.1.
have hPositive:=@current_mass_density_nonnegative R h2 n m U gamma hGamma xi.
have hNormMeas:=@current_density_mass_measurable R h2 n m UT gamma hGamma xi hField.1.
have hLambda:=@measure_with_density_is_measure R UT gamma hGamma H hPositive.
have hLambdaRadon:=@current_mass_density_radon R h2 n m U hU gamma hGamma hRadon xi hField.
have hAction:is_distribution_integral_action lambda ed w dvalues
    (@current_value R h2 n U hU m T).
  move=>psi.
  have [c hPair]:=@current_unit_density_test_integral_finite R h2 n m U hU
    gamma hGamma hRadon w hW hUnit psi.
  have hPoint:(fun x=>ed (w x) (dvalues psi x)*VN (xi x))=
      (fun x=>ed (xi x) (dvalues psi x)).
    apply:funext=>x.
    have h:=congr1 (fun v=>ed v (dvalues psi x)) (hReconstruct x).
    rewrite linearZ hom_scaleE in h.
    by rewrite mulrC;exact:h.
  have hProduct:is_measure_integral gamma
      (real_total_integrand (fun x=>ed (w x) (dvalues psi x)*VN (xi x)))
      (@current_value R h2 n U hU m T psi)%:E.
    rewrite hPoint;exact:distribution_representation_action hRep psi.
  exact:((@real_finite_density_integral_iff R UT gamma lambda hGamma (fun x=>VN (xi x))
    (fun x=>ed (w x) (dvalues psi x)) (measure_with_density_laws gamma H) hNormMeas
    hPositive hPair.1 _).2 hProduct).
have hNormal:=@NormalisedCurrent.laws R h2 n m U hU T hT.
have hBase:=normalised_distribution_representation_laws hNormal.
have hVariation:=@current_represented_original_variation R h2 n m U hU
  gamma hGamma hRadon xi hField T hRep hT.
rewrite hVariation in hBase.
have hEqual:=@bounded_current_density_almost_unique R h2 n m U hU lambda hLambda hLambdaRadon
  w theta hWL (distribution_representation_weak_measurable hBase) hUnit
  (normalised_distribution_density_unit_bound hNormal)
  (@current_value R h2 n U hU m T) hAction (distribution_representation_action hBase).
exists w;split;first exact:hW.
split;first exact:hWL.
split;first exact:hUnit.
split;[exact:hReconstruct|exact:hEqual].
Qed.
End CurrentRepresentedUnitDensity.
