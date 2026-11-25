(** Federer (1969), 4.1.8, p. 361: the original
    binomial lower variation bound, and equality under the
    original pointwise either-simple condition on normalized
    factors. All assertions retain arbitrary target sets
    and both zero or infinite measure values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianDensityMeasurable CurrentCartesianDensityIntegrable CurrentCartesianDensityCurrent
  CurrentCartesianProductUnique CurrentCartesianProductSealed OpenCurrentDensityUP OpenCurrentDensitySealed
  RadonMeasureUP NormalisedCurrentSealed CurrentRepresentedDensityVariation CurrentCartesianProductRepresentation
  CurrentCartesianVectorMassUpper CurrentCartesianDomainMapsSealed
  CurrentCartesianVariationUpper CurrentCartesianDensityAlmost FinitePositiveDensityLower
  MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureDensityTransfer MeasureDensityUP SimpleVectors
  CurrentCoefficientNorms RealNormUP MeasureDensity RealFiniteDensityIntegral
  NonnegativeDensitySetUpperBound RadonBorelRegularity BorelRegularMeasureUP
  CurrentCartesianProductUP CurrentCartesianTestProductSealed CurrentDegreeTransport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegralFieldUP MeasureUP ProductMeasure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialFunctionBasic PartialFunctionPrecomposition
  SummableRealFunctionUP SummableRealArithmetic SeparatedProductIntegral MeasureBijectionIntegralTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVariationComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) AB).
Local Notation PT := (Choice.clone (AT*BT)%type _).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation va := (fun k=>@current_test_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Variables (xi:AT->exterior_power X i) (eta:BT->exterior_power Y j).
Hypothesis hS:@is_normalised_current_representation R h2 m i A hA S alpha xi.
Hypothesis hT:@is_normalised_current_representation R h2 n j B hB T beta eta.
Local Notation hBaseS := (normalised_distribution_representation_laws hS).
Local Notation hBaseT := (normalised_distribution_representation_laws hT).
Local Notation hAlpha := (distribution_representation_measure hBaseS).
Local Notation hBeta := (distribution_representation_measure hBaseT).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation zeta := (@current_cartesian_density R m n i j A B xi eta).
Local Notation hBij := (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta).

Local Notation P := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).


Local Notation H := (real_total_integrand (fun z=>@current_vector_mass R h2 (m+n) (i+j) (zeta z))).
Local Notation hLambda := (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta).
Local Notation hRadon := (@current_cartesian_measure_radon R m n A B hA hB alpha beta hAlpha hBeta
  (distribution_representation_radon hBaseS) (distribution_representation_radon hBaseT)).
Local Notation hField := (@current_cartesian_density_locally_integrable R h2 m n i j A B hA hB
  alpha beta hAlpha hBeta (distribution_representation_radon hBaseS)
  (distribution_representation_radon hBaseT) xi eta
  (distribution_representation_weak_measurable hBaseS)
  (distribution_representation_weak_measurable hBaseT)
  (normalised_distribution_density_unit_bound hS) (normalised_distribution_density_unit_bound hT)).
Variable hP:@is_integration_representable_current R h2 (m+n) (i+j) AB hAB P.
Local Notation nu := (@NormalisedCurrent.measure R h2 (m+n) (i+j) AB hAB P hP).


(** Source for [current_cartesian_product_variation_lower]:
    the printed binomial coefficient times ||S times T||
    dominates the original product ||S|| times ||T||,
    Federer 4.1.8, p. 361. No simplicity premise is used. *)
Theorem current_cartesian_product_variation_lower E:
  (lambda E<='C(i+j,i)%:R%:E*nu E)%E.
Proof.
rewrite (@current_cartesian_product_variation_formula R h2 m n i j A B hA hB
  S T alpha beta xi eta hS hT hP).
have hCoefficient:(0<('C(i+j,i)%:R:R)) by rewrite ltr0n bin_gt0;exact:leq_addr.
exact:(@finite_positive_density_lower R CT lambda (measure_with_density lambda H) hLambda
  (fun z=>@current_vector_mass R h2 (m+n) (i+j) (zeta z)) (measure_with_density_laws lambda H)
  (fun z=>real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 (m+n) (i+j)).1 _)
  'C(i+j,i)%:R hCoefficient
  (@current_cartesian_density_binomial_almost R h2 m n i j A B hA hB
    S T alpha beta xi eta hS hT) E).
Qed.

(** Source for [current_cartesian_product_variation_simple_equality]:
    either simple factor at almost every original product
    point gives ||S times T||=||S|| times ||T||,
    supporting Federer 4.1.8, p. 361. The disjunction is
    pointwise and does not require both factors simple. *)
Theorem current_cartesian_product_variation_simple_equality:
  measure_almost_everywhere lambda [set z:CT|
    simple (xi (D z).1) \/simple (eta (D z).2)] ->nu= lambda.
Proof.
move=>hSimple.
have hUnit:=@current_cartesian_density_simple_unit_almost R h2 m n i j A B hA hB
  S T alpha beta xi eta hS hT hSimple.
have hEqual:measure_almost_equal lambda H (real_total_integrand (fun _=>1)).
  apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _ hUnit)=>z hz.
  exists (1:R)%:E;split;by rewrite real_total_integrand_graph ?hz.
have hOriginalDensity:is_measure_density lambda H nu.
  rewrite (@current_cartesian_product_variation_formula R h2 m n i j A B hA hB
    S T alpha beta xi eta hS hT hP);exact:measure_with_density_laws.
have hOne:=measure_density_almost_equal hLambda hOriginalDensity hEqual.
have hRegular:=borel_regular_is_regular hLambda (radon_borel_regular hLambda hRadon).
apply:funext=>E;exact:(@regular_measure_unit_density_value R CT lambda nu hLambda hRegular hOne E).
Qed.
End CurrentCartesianVariationComparison.
