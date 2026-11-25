(** Federer (1969), 4.1.7, p. 358:
    gamma wedge xi has a unit density with
    respect to gamma restricted by mass(xi).
    This supporting step uses the earlier finite
    norm normalization and exact change-of-density
    identity. It does not replace the original gauge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RadonMeasureUP Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  CurrentIntegrationCriterion OpenCurrentDensityUP OpenCurrentDensitySealed CurrentNormDensityRadon
  CurrentDensityNormMeasurable CurrentDensityNormalisation CurrentUnitDensityTestIntegral
  OpenFamilyTopologyMathcomp PartialFunctionBasic SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureDensity
  MeasureDensityTransfer RealFiniteDensityIntegral MeasureIntegralUP
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionIntegralFieldUP
  DistributionIntegrationRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDensityNormalisedAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT (smooth_test_values_hom hE)).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).
Local Notation T := (@OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon xi hField).
Local Notation S := (@current_value R h2 n U hU m T).

(** Source for [current_mass_density_unit_representation]:
    the original current has a weakly measurable
    mass-one density almost everywhere with respect
    to the literal mass-density measure, supporting
    Federer 4.1.7, p. 358. The zero-density
    locus has zero weighted measure; it is not
    discarded from the original definition of xi. *)
Theorem current_mass_density_unit_representation:
  exists w:UT->V,
    is_measure_measurable_function lambda
      (partial_function_total (fun x=>(w x:open_family_topological_space hO.1))) /\
    (forall x,VN (w x)<=1) /\
    measure_almost_everywhere lambda [set x|VN (w x) = 1] /\
    is_distribution_integral_action lambda ed w dvalues S.
Proof.
have [w [hW [hUnit [hReconstruct hUnitNonzero]]]]:=
  @current_density_normalisation_exists R h2 n m UT gamma hGamma xi hField.1.
have hPositive:=@current_mass_density_nonnegative R h2 n m U gamma hGamma xi.
have hNormMeas:=@current_density_mass_measurable R h2 n m UT gamma hGamma xi hField.1.
have hRepresentation:=@OpenCurrentDensity.laws R h2 n m U hU gamma hGamma hRadon xi hField.
have hZero:=@finite_real_density_zero_locus_null R UT gamma lambda hGamma
  (fun x=>VN (xi x)) (measure_with_density_laws gamma H).
have hAlmost:measure_almost_everywhere lambda [set x|VN (w x) = 1].
  apply:(@measure_null_subset R UT lambda (measure_with_density_is_measure hGamma hPositive)
    _ _ _ hZero)=>x hx.
  case:(eqVneq (VN (xi x)) 0)=>h; first exact:h.
  exfalso; exact:hx (hUnitNonzero x h).
have hWeakLambda:=@measure_density_measurable_function R UT (open_family_topological_space hO.1)
  gamma lambda hGamma H (partial_function_total (fun x=>(w x:open_family_topological_space hO.1)))
  (measure_with_density_laws gamma H) hPositive hW.
exists w; split; first exact:hWeakLambda.
split; first exact:hUnit.
split; first exact:hAlmost.
move=>psi.
have [c hPair]:=@current_unit_density_test_integral_finite R h2 n m U hU gamma hGamma hRadon
  w hW hUnit psi.
have hOriginal:=distribution_representation_action hRepresentation psi.
have hPoint:(fun x=>ed (w x) (dvalues psi x)*VN (xi x))=
    (fun x=>ed (xi x) (dvalues psi x)).
  apply:funext=>x.
  have h:=congr1 (fun v=>ed v (dvalues psi x)) (hReconstruct x).
  rewrite linearZ hom_scaleE in h.
  by rewrite mulrC; exact:h.
have hProduct:is_measure_integral gamma
    (real_total_integrand (fun x=>ed (w x) (dvalues psi x)*VN (xi x))) (S psi)%:E.
  by rewrite hPoint.
exact:((@real_finite_density_integral_iff R UT gamma lambda hGamma (fun x=>VN (xi x))
  (fun x=>ed (w x) (dvalues psi x)) (measure_with_density_laws gamma H) hNormMeas
  hPositive hPair.1 (S psi)%:E).2 hProduct).
Qed.
End CurrentDensityNormalisedAction.
