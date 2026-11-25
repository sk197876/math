(** Federer (1969), 4.1.8, p. 361: the original
    product variation comparisons and the equality and
    orientation conclusions under the original pointwise
    either-simple hypothesis. All orientation domains remain
    the actual original partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap SimpleVectors
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion CurrentMultivectorDual
  NormalisedCurrentSealed MultivectorDualSealed CurrentOrientationSealed CurrentOrientationAlmost
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentCartesianDensityMeasurable
  CurrentCartesianProductSealed CurrentCartesianProductRepresentation CurrentCartesianOrientationProduct
  CurrentCartesianVariationUpper CurrentCartesianVariationComparison CurrentOriginalDensityAgreement
  CurrentCartesianOriginalDensity MeasureAlmostEquality
  CartesianMeasureAlmost DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP ProductMeasure MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianOriginalComparison.
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
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Hypothesis hS:@is_integration_representable_current R h2 m i A hA S.
Hypothesis hT:@is_integration_representable_current R h2 n j B hB T.
Local Notation alpha := (@NormalisedCurrent.measure R h2 m i A hA S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j B hB T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 m i A hA S hS).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j B hB T hT).
Local Notation hNS := (@NormalisedCurrent.laws R h2 m i A hA S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j B hB T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation hLambda := (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta).
Local Notation hBij := (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta).
Local Notation zeta := (@current_cartesian_density R m n i j A B xi eta).
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).
Local Notation OS := (@CurrentOrientation.value R h2 m i A hA S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j B hB T hT).
Local Notation Gamma := (@current_cartesian_orientation_product R m n i j A B OS OT).
Local Notation ed := (@MultivectorDual.evaluation R Z (i+j)).
Local Notation DT := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation v := (@current_test_value R h2 (m+n) AB hAB (i+j)).


Variable hP:@is_integration_representable_current R h2 (m+n) (i+j) AB hAB P.
Local Notation nu := (@NormalisedCurrent.measure R h2 (m+n) (i+j) AB hAB P hP).
Local Notation OP := (@CurrentOrientation.value R h2 (m+n) (i+j) AB hAB P hP).
Local Notation simple_pair := [set z:CT|exists a,exists b,
  partial_function_graph OS (D z).1 a /\partial_function_graph OT (D z).2 b /\
    (simple a \/simple b)].

(** Source for [current_cartesian_original_variation_upper]:
    the original product-current variation is at most the
    product of the two original variation measures on every
    set, Federer 4.1.8, p. 361. *)
Theorem current_cartesian_original_variation_upper E:(nu E<=lambda E)%E.
Proof.
exact:(@current_cartesian_product_variation_upper R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT hP E).
Qed.

(** Source for [current_cartesian_original_variation_lower]:
    the original product measure is at most the printed
    binomial coefficient times the original product-current
    variation, Federer 4.1.8, p. 361. Infinite masses
    and both degree-zero endpoints remain included. *)
Theorem current_cartesian_original_variation_lower E:
  (lambda E<='C(i+j,i)%:R%:E*nu E)%E.
Proof.
exact:(@current_cartesian_product_variation_lower R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT hP E).
Qed.

(** Source for [current_cartesian_original_variation_equality]:
    if either original factor orientation is simple at
    almost every product point, the original product
    variation equals the product of the original factor
    variations, Federer 4.1.8, p. 361. *)
Theorem current_cartesian_original_variation_equality:
  measure_almost_everywhere lambda simple_pair ->nu= lambda.
Proof.
move=>hSimple.
have hAux:=@current_cartesian_original_simple_transfer R h2 m n i j A B hA hB S T hS hT hSimple.
exact:(@current_cartesian_product_variation_simple_equality R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT hP hAux).
Qed.

(** Source for [current_cartesian_original_orientation_equality]:
    under that same pointwise either-simple condition, the
    original product orienting field is almost equal to
    the displayed original partial product field, Federer
    4.1.8, p. 361. Neither field is replaced by a
    chosen total extension. *)
Theorem current_cartesian_original_orientation_equality:
  measure_almost_everywhere lambda simple_pair ->measure_almost_equal lambda OP Gamma.
Proof.
move=>hSimple.
have hVariation:=current_cartesian_original_variation_equality hSimple.
have hRep:=@current_cartesian_original_representation R h2 m n i j A B hA hB S T hS hT.
have hBound:=@current_cartesian_product_density_unit_bound R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT.
have hOrientation:=@current_original_unit_density_agreement R h2 (m+n) (i+j) AB hAB P hP
  lambda zeta hRep hBound hVariation.
have hGamma:=@current_cartesian_original_density_agreement R h2 m n i j A B hA hB S T hS hT.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda hOrientation hGamma))=>z [hO hG].
exists (zeta z);by split.
Qed.
End CurrentCartesianOriginalComparison.
