(** Federer (1969), 4.1.8, p. 361: original
    Radon-density and orienting-field formulas for the
    Cartesian product. Retain the actual maximal factor
    orientations and their original partial domains. The
    auxiliary normalized densities are used only in proofs. *)
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
  CartesianMeasureAlmost DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP ProductMeasure MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianOriginalDensity.
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

(** Source for [current_cartesian_original_representation]:
    the product current has the original product Radon
    representation, supporting Federer 4.1.8, p. 361.
    Both factors need only their original representability. *)
Theorem current_cartesian_original_representation:
  @is_current_integration_representation R h2 (m+n) (i+j) AB hAB P lambda zeta.
Proof.
exact:(@current_cartesian_product_normalised_representation R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT).
Qed.

(** Source for [current_cartesian_original_representable]:
    the original product is representable by integration,
    Federer 4.1.8, p. 361. *)
Theorem current_cartesian_original_representable:
  @is_integration_representable_current R h2 (m+n) (i+j) AB hAB P.
Proof. exists lambda,zeta;exact:current_cartesian_original_representation. Qed.

(** Source for [current_cartesian_original_factor_agreement]:
    both original maximal factor orientations agree with
    the auxiliary normalized densities at almost every
    original product point, supporting Federer 4.1.8,
    p. 361, through 4.1.7, p. 357. *)
Theorem current_cartesian_original_factor_agreement:
  measure_almost_everywhere lambda [set z:CT|
    partial_function_graph OS (D z).1 (xi (D z).1) /\
    partial_function_graph OT (D z).2 (eta (D z).2)].
Proof.
have hFirst:=@product_almost_everywhere_first_factor R AT BT alpha beta hAlpha hBeta _
  (@current_orientation_normalised_agreement R h2 m i A hA S hS).
have hSecond:=@product_almost_everywhere_second_factor R AT BT alpha beta hAlpha hBeta _
  (@current_orientation_normalised_agreement R h2 n j B hB T hT).
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _
  (measure_almost_everywhere_and hm hFirst hSecond))=>z [hX hY].
change (partial_function_graph OS (D (J z)).1 (xi (D (J z)).1) /\
  partial_function_graph OT (D (J z)).2 (eta (D (J z)).2)).
by rewrite current_cartesian_domain_join_split.
Qed.

(** Source for [current_cartesian_original_density_agreement]:
    the original partial product field has the actual
    normalized coefficient almost everywhere, supporting
    Federer 4.1.8, p. 361. Its precise domain is retained. *)
Theorem current_cartesian_original_density_agreement:
  measure_almost_everywhere lambda [set z:CT|partial_function_graph Gamma z (zeta z)].
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  current_cartesian_original_factor_agreement)=>z [hX hY].
apply:((@current_cartesian_orientation_product_graph R m n i j A B OS OT z (zeta z)).2).
exists (xi (D z).1),(eta (D z).2);by split=>//;split.
Qed.

(** Source for [current_cartesian_oriented_test_pairing]:
    the original partial integrand <phi,zeta>, Federer
    4.1.8, p. 361. It is defined exactly where both
    original factor orienting fields are defined. *)
Definition current_cartesian_oriented_test_pairing (phi:DT):partial_function CT (\bar R):=
  partial_function_postcompose
    (partial_function_pair Gamma (partial_function_total (fun z=>v phi (set_val z))))
    (fun vy=>(ed vy.1 vy.2)%:E).

(** Source for [current_cartesian_original_integral_action]:
    the product current is literally the integral of the
    displayed original partial product density against the
    original product variation measure, Federer 4.1.8,
    p. 361. Every original compact test is included. *)
Theorem current_cartesian_original_integral_action phi:
  is_measure_integral lambda (current_cartesian_oriented_test_pairing phi)
    (@current_value R h2 (m+n) AB hAB (i+j) P phi)%:E.
Proof.
apply:(@measure_integral_almost_equal R CT lambda hLambda
  (real_total_integrand (fun z=>ed (zeta z) (v phi (set_val z))))
  (current_cartesian_oriented_test_pairing phi) _
  (distribution_representation_action current_cartesian_original_representation phi)).
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  current_cartesian_original_density_agreement)=>z hz.
exists (ed (zeta z) (v phi (set_val z)))%:E;split;first by rewrite real_total_integrand_graph.
exists (zeta z,v phi (set_val z));split;first by split.
by [].
Qed.

(** Source for [current_cartesian_original_simple_transfer]:
    the printed pointwise disjunction on the actual
    original orienting fields transfers to the auxiliary
    factors almost everywhere, supporting Federer 4.1.8,
    p. 361. No global choice of a simple side is required. *)
Theorem current_cartesian_original_simple_transfer:
  measure_almost_everywhere lambda [set z:CT|exists a,exists b,
    partial_function_graph OS (D z).1 a /\partial_function_graph OT (D z).2 b /\
      (simple a \/simple b)] ->
  measure_almost_everywhere lambda [set z:CT|simple (xi (D z).1) \/simple (eta (D z).2)].
Proof.
move=>hSimple.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda current_cartesian_original_factor_agreement hSimple))
  =>z [[hX hY] [a [b [hAValue [hBValue hSimp]]]]].
have hAEqual:=partial_function_single_valued hAValue hX.
have hBEqual:=partial_function_single_valued hBValue hY.
change (simple (xi (D z).1) \/simple (eta (D z).2)).
by rewrite -hAEqual -hBEqual.
Qed.
End CurrentCartesianOriginalDensity.
