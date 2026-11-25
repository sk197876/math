(** Federer (1969), 4.1.8, p. 361, used in
    4.1.12, p. 369: the total mass of the
    original Cartesian product is at most the product
    of the original factor masses. Reuse the exact
    Radon variation comparison and product measure law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentDomain CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentCartesianOriginalDensity CurrentCartesianVariationUpper CurrentCartesianMeasureRadon
  CurrentCartesianMeasureSealed CurrentCartesianDomainMapsSealed CurrentMassSealed CurrentMassRepresentation
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP MeasureUP MeasureBasic
  MeasureSplit ProductMeasure MeasurePushforward MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianMassBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
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
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).

(** Source for [current_cartesian_mass_bound]:
    M(S times T)<=M(S)M(T), the total-mass consequence
    of the first variation inequality in Federer
    4.1.8, p. 361, used for the first flat
    product estimate in 4.1.12, p. 369.
    Retain the original ordinary partial-product domain. *)
Theorem current_cartesian_mass_bound:
  mule_def (@CurrentMass.value R h2 m i A hA S) (@CurrentMass.value R h2 n j B hB T)->
  (@CurrentMass.value R h2 (m+n) (i+j) AB hAB P<=
    @CurrentMass.value R h2 m i A hA S * @CurrentMass.value R h2 n j B hB T)%E.
Proof.
move=>hDef.
pose hP:=@current_cartesian_original_representable R h2 m n i j A B hA hB S T hS hT.
rewrite (@current_represented_mass_total R h2 (m+n) (i+j) AB hAB P hP)
  (@current_represented_mass_total R h2 m i A hA S hS)
  (@current_represented_mass_total R h2 n j B hB T hT).
apply:(le_trans (@current_cartesian_product_variation_upper R h2 m n i j A B hA hB
  S T alpha beta xi eta hNS hNT hP setT)).
have hBij:=@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta.
rewrite -(measure_bijection_pushforward hBij) /measure_pushforward preimage_setT.
have hRectangle:=@product_measure_rectangle_bound R _ _ alpha beta hAlpha hBeta setT setT
  (@measure_measurable_whole R _ alpha hAlpha) (@measure_measurable_whole R _ beta hBeta).
by rewrite setXTT in hRectangle.
Qed.
End CurrentCartesianMassBound.
