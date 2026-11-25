(** Federer (1969), 4.1.9, p. 363: the actual
    time-product current has exactly the original product
    variation and the positive time vector wedged with the
    original partial orientation of T. Simplicity is used
    only for the unit time factor, as in 4.1.8, p. 361. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate ExteriorGrading ExteriorPowers
  FiniteExteriorPowers EuclideanCartesianMap SimpleElementary SimpleVectors CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentCartesianDensityMeasurable CurrentCartesianVectorProduct
  CurrentCartesianProductSealed CurrentCartesianOriginalDensity CurrentCartesianOriginalComparison
  CurrentCartesianOrientationProduct CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  NormalisedCurrentSealed CurrentOrientationSealed CurrentSegmentMeasureSealed ScalarSegmentCoordinateValues
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CartesianMeasureAlmost PartialFunctionUP MeasureAlmostUP MeasureAlmostBasic ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyProductOrientation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation S := (@current_homotopy_time_segment R A hA h2).
Local Notation hS := (@current_homotopy_time_representable R h2 A hA).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation TT := (current_domain R 1%N AT).
Local Notation XT := (current_domain R n U).
Local Notation AU := (@euclidean_cartesian_set R 1%N n AT U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation CT := (current_domain R (1+n)%N AU).
Local Notation PT := (Choice.clone (TT*XT)%type _).
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation hNS := (@NormalisedCurrent.laws R h2 1%N 1%N AT hAT S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j U hU T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation lambda := (@CartesianCurrentMeasure.value R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation hLambda := (@current_cartesian_measure_is_measure R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation J := (@CartesianCurrentDomain.join R 1%N n AT U).
Local Notation D := (@CartesianCurrentDomain.split R 1%N n AT U).
Local Notation hBij := (@current_cartesian_measure_bijection R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N)
  (@euclidean_one_embed R 1-@euclidean_one_embed R 0)).
Local Notation OS := (@CurrentOrientation.value R h2 1%N 1%N AT hAT S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j U hU T hT).
Local Notation P := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).
Local Notation Product := (@current_cartesian_vector_product R 1%N n 1%N j).

(** Source for [current_homotopy_time_simple]: the actual
    positive unit time vector is simple, supporting the
    represented homotopy calculation in Federer 4.1.9,
    p. 363. No simplicity of T is assumed. *)
Theorem current_homotopy_time_simple:simple velocity.
Proof.
rewrite scalar_segment_velocity subr0 scale1r.
exact:product_simple.
Qed.

(** Source for [current_homotopy_product_time_orientation]:
    the actual product has the positive unit time field
    at almost every original product point, supporting
    Federer 4.1.9, p. 363. The field remains partial. *)
Theorem current_homotopy_product_time_orientation:
  measure_almost_everywhere lambda [set z:CT|partial_function_graph OS (D z).1 velocity].
Proof.
have hTime:=@current_homotopy_time_original_orientation R h2 A hA hS.
rewrite -(@current_homotopy_time_variation R h2 A hA hS) in hTime.
have hFirst:=@product_almost_everywhere_first_factor R TT XT alpha beta hAlpha hBeta _ hTime.
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _ hFirst)=>z hz.
change (partial_function_graph OS (D (J z)).1 velocity).
by rewrite current_cartesian_domain_join_split.
Qed.

(** Source for [current_homotopy_product_simple_pair]: the
    first orientation supplies the exact either-simple
    hypothesis of 4.1.8, p. 361, supporting the original
    homotopy measure calculation in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_product_simple_pair:
  measure_almost_everywhere lambda [set z:CT|exists a,exists b,
    partial_function_graph OS (D z).1 a /\partial_function_graph OT (D z).2 b /\
      (simple a \/simple b)].
Proof.
have hFactors:=@current_cartesian_original_factor_agreement R h2 1%N n 1%N j AT U hAT hU S T hS hT.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda current_homotopy_product_time_orientation hFactors))
  =>z [hTime [hFirst hSecond]].
exists velocity,(eta (D z).2);split=>//;split=>//.
left;exact:current_homotopy_time_simple.
Qed.

(** Source for [current_homotopy_product_variation]: the
    time-product variation is exactly the product of the
    original time and T variation measures on every set,
    supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_product_variation
    (hP:@is_integration_representable_current R h2 (1+n)%N (1+j) AU hAU P):
  @NormalisedCurrent.measure R h2 (1+n)%N (1+j) AU hAU P hP=lambda.
Proof.
exact:(@current_cartesian_original_variation_equality R h2 1%N n 1%N j AT U hAT hU
  S T hS hT hP current_homotopy_product_simple_pair).
Qed.

(** Source for [current_homotopy_product_orientation]: the
    original partial product orientation equals the positive
    time vector wedged with the original partial orientation
    of T almost everywhere, supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_product_orientation
    (hP:@is_integration_representable_current R h2 (1+n)%N (1+j) AU hAU P):
  measure_almost_everywhere lambda [set z:CT|exists a,
    partial_function_graph OT (D z).2 a /\
    partial_function_graph (@CurrentOrientation.value R h2 (1+n)%N (1+j) AU hAU P hP) z (Product velocity a)].
Proof.
have hOriginal:=@current_cartesian_original_orientation_equality R h2 1%N n 1%N j AT U hAT hU
  S T hS hT hP current_homotopy_product_simple_pair.
have hFactors:=@current_cartesian_original_factor_agreement R h2 1%N n 1%N j AT U hAT hU S T hS hT.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda hOriginal
    (measure_almost_everywhere_and hLambda current_homotopy_product_time_orientation hFactors)))
  =>z [[w [hW hGamma]] [hTime [hFirst hSecond]]].
exists (eta (D z).2);split;first exact:hSecond.
have hProduct:partial_function_graph
    (@current_cartesian_orientation_product R 1%N n 1%N j AT U OS OT) z (Product velocity (eta (D z).2)).
  apply:((@current_cartesian_orientation_product_graph R 1%N n 1%N j AT U OS OT z _).2).
  exists velocity,(eta (D z).2);split=>//;split=>//.
have hEqual:=partial_function_single_valued hGamma hProduct.
by rewrite -hEqual.
Qed.
End CurrentHomotopyProductOrientation.
