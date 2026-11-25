(** Federer (1969), 4.1.8, p. 361: the original
    product variation is the original product measure
    weighted by the actual product-density mass, and is
    bounded above by that original measure on every set. *)
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
Section CurrentCartesianVariationUpper.
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

(** Source for [current_cartesian_product_variation_formula]:
    the original product variation equals the product Radon
    measure weighted by the actual coefficient mass,
    supporting Federer 4.1.8, p. 361, through 4.1.7,
    p. 358. Every outer-measure value is retained. *)
Theorem current_cartesian_product_variation_formula:nu= measure_with_density lambda H.
Proof.
exact:(@current_represented_original_variation R h2 (m+n) (i+j) AB hAB lambda
  hLambda hRadon zeta hField P
  (@current_cartesian_product_normalised_representation R h2 m n i j A B hA hB
    S T alpha beta xi eta hS hT) hP).
Qed.

(** Source for [current_cartesian_product_density_unit_bound]:
    the original normalized product coefficient has mass
    at most one everywhere, supporting the first variation
    inequality of Federer 4.1.8, p. 361. *)
Lemma current_cartesian_product_density_unit_bound z:
  @current_vector_mass R h2 (m+n) (i+j) (zeta z)<=1.
Proof.
rewrite /current_cartesian_density.
apply:le_trans (@current_cartesian_vector_mass_upper R h2 m n i j _ _) _.
apply:le_trans (ler_wpM2r (real_seminorm_nonnegative
  (@current_vector_mass_real_norm R h2 n j).1 _)
  (normalised_distribution_density_unit_bound hS _)) _.
rewrite mul1r;exact:(normalised_distribution_density_unit_bound hT (D z).2).
Qed.

(** Source for [current_cartesian_product_variation_upper]:
    ||S times T|| is at most ||S|| times ||T||,
    Federer 4.1.8, p. 361, first displayed comparison.
    Arbitrary target sets and infinite masses are included. *)
Theorem current_cartesian_product_variation_upper E:(nu E<=lambda E)%E.
Proof.
rewrite current_cartesian_product_variation_formula.
have hRegular:=borel_regular_is_regular hLambda (radon_borel_regular hLambda hRadon).
have hDensity:=real_finite_density_total_laws (measure_with_density_laws lambda H).
have hBound:=@nonnegative_density_set_upper_bound R CT lambda (measure_with_density lambda H)
  hLambda (fun z=>(@current_vector_mass R h2 (m+n) (i+j) (zeta z))%:E)
  E 1 hRegular hDensity (@ltr01 R).
have hUpper:forall z,E z->
    ((@current_vector_mass R h2 (m+n) (i+j) (zeta z))%:E<=1%:E)%E.
  move=>z _;rewrite lee_fin;exact:current_cartesian_product_density_unit_bound.
by have:=hBound hUpper;rewrite mul1e.
Qed.
End CurrentCartesianVariationUpper.
