(** Federer (1969), 4.1.8, p. 361: the original
    Cartesian product of integration-representable currents
    has the original Radon product-density representation.
    Existence is proved by the earlier actual density-current
    theorem, and the original product uniqueness identifies it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianDensityMeasurable CurrentCartesianDensityIntegrable CurrentCartesianDensityCurrent
  CurrentCartesianProductUnique CurrentCartesianProductSealed OpenCurrentDensityUP OpenCurrentDensitySealed
  RadonMeasureUP
  CurrentCartesianProductUP CurrentCartesianTestProductSealed CurrentDegreeTransport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegralFieldUP MeasureUP ProductMeasure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialFunctionBasic PartialFunctionPrecomposition
  SummableRealFunctionUP SummableRealArithmetic SeparatedProductIntegral MeasureBijectionIntegralTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianProductRepresentation.
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

(** Source for [current_cartesian_product_normalised_representation]:
    the product current integrates the original included
    exterior-product density against the original product
    of the factor variation measures, Federer 4.1.8,
    p. 361. This statement retains every original test. *)
Theorem current_cartesian_product_normalised_representation:
  @is_current_integration_representation R h2 (m+n) (i+j) AB hAB P lambda zeta.
Proof.
have hRadon:=@current_cartesian_measure_radon R m n A B hA hB alpha beta hAlpha hBeta
  (distribution_representation_radon hBaseS) (distribution_representation_radon hBaseT).
have hField:=@current_cartesian_density_locally_integrable R h2 m n i j A B hA hB
  alpha beta hAlpha hBeta (distribution_representation_radon hBaseS)
  (distribution_representation_radon hBaseT) xi eta
  (distribution_representation_weak_measurable hBaseS)
  (distribution_representation_weak_measurable hBaseT)
  (normalised_distribution_density_unit_bound hS) (normalised_distribution_density_unit_bound hT).
pose C:=@OpenCurrentDensity.value R h2 (m+n) (i+j) AB hAB lambda
  (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta) hRadon zeta hField.
have hC:=@OpenCurrentDensity.laws R h2 (m+n) (i+j) AB hAB lambda
  (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta) hRadon zeta hField.
have hSpec:=@current_cartesian_density_current_characterisation R h2 m n i j A B hA hB
  S T alpha beta xi eta hS hT C hC.
have hEqual:=@current_cartesian_product_unique R h2 m n i j A B hA hB S T C P hSpec
  (@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).
rewrite -hEqual;exact:hC.
Qed.

(** Source for [current_cartesian_product_integration_representable]:
    the original product of representable currents is
    representable by integration, Federer 4.1.8, p. 361.
    The displayed original density and measure are witnesses. *)
Theorem current_cartesian_product_integration_representable:
  @is_integration_representable_current R h2 (m+n) (i+j) AB hAB P.
Proof. exists lambda,zeta;exact:current_cartesian_product_normalised_representation. Qed.
End CurrentCartesianProductRepresentation.
