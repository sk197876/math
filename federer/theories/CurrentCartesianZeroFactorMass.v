(** Federer (1969), 4.1.23, p. 380:
    a zero-degree Cartesian factor preserves
    the exact product of finite masses.
    The preceding all-set binomial lower
    bound has coefficient one in this
    degree, so no simplicity witness or
    auxiliary orientation premise is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentDomain CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianOriginalDensity
  CurrentCartesianVariationComparison CurrentCartesianMeasureSealed
  CurrentCartesianMeasureRadon CurrentCartesianFiniteMassBound
  CurrentMassSealed CurrentMassRepresentation CurrentFiniteMassRepresentation
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP MeasureUP MeasureBasic ProductMeasure
  ProductRectangleValue MeasurePushforward MeasureBijectionUP.
From Federer Require Import MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ZeroFactorMass.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m n i : nat.
Variables (A : set (R_n R m)) (B : set (R_n R n)).
Hypothesis hA : forall x, A x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB : forall x, B x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B x.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Variable S : @current_space R h2 m A hA i.
Variable T : @current_space R h2 n B hB 0%N.
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i 0%N A B hA hB S T).

(** Source for [current_cartesian_zero_factor_mass]:
    M(R times Q)=M(R)M(Q), and
    likewise for the transverse Lebesgue
    zero-current S, Federer 4.1.23,
    p. 380. Both masses are
    finite here, with zero and
    empty-domain cases retained. *)
Theorem current_cartesian_zero_factor_mass (a b : R) :
  @CurrentMass.value R h2 m i A hA S=a%:E ->
  @CurrentMass.value R h2 n 0%N B hB T=b%:E ->
  @CurrentMass.value R h2 (m+n) (i+0) AB hAB P=(a*b)%:E.
Proof.
move=> hMassS hMassT.
have hSF : (@CurrentMass.value R h2 m i A hA S< +oo)%E by rewrite hMassS ltry.
have hTF : (@CurrentMass.value R h2 n 0%N B hB T< +oo)%E by rewrite hMassT ltry.
pose hS := @current_finite_mass_representation R h2 m i A hA S hSF.
pose hT := @current_finite_mass_representation R h2 n 0%N B hB T hTF.
pose alpha := @NormalisedCurrent.measure R h2 m i A hA S hS.
pose beta := @NormalisedCurrent.measure R h2 n 0%N B hB T hT.
pose xi := @NormalisedCurrent.auxiliary_density R h2 m i A hA S hS.
pose eta := @NormalisedCurrent.auxiliary_density R h2 n 0%N B hB T hT.
pose hNS := @NormalisedCurrent.laws R h2 m i A hA S hS.
pose hNT := @NormalisedCurrent.laws R h2 n 0%N B hB T hT.
pose hAlpha := distribution_representation_measure (normalised_distribution_representation_laws hNS).
pose hBeta := distribution_representation_measure (normalised_distribution_representation_laws hNT).
pose lambda := @CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta.
pose hP := @current_cartesian_original_representable R h2 m n i 0%N A B hA hB S T hS hT.
have hLambda : lambda setT=(a*b)%:E.
  have hBij := @current_cartesian_measure_bijection R m n A B
    alpha beta hAlpha hBeta.
  rewrite /lambda -(measure_bijection_pushforward hBij)
    /measure_pushforward preimage_setT -setXTT.
  rewrite (@product_measure_rectangle_value R AT BT alpha beta hAlpha hBeta setT setT
    (measure_measurable_whole hAlpha) (measure_measurable_whole hBeta)).
  rewrite /alpha /beta -(@current_represented_mass_total R h2 m i A hA S hS)
    -(@current_represented_mass_total R h2 n 0%N B hB T hT) hMassS hMassT -EFinM.
  reflexivity.
have hLower := @current_cartesian_product_variation_lower R h2 m n i 0%N A B hA hB
  S T alpha beta xi eta hNS hNT hP setT.
have hCoefficient : ('C(i+0,i)%:R:R)= 1 by rewrite addn0 binn.
rewrite hCoefficient mul1e in hLower.
change (is_true (lambda setT<=@NormalisedCurrent.measure R h2 (m+n) (i+0) AB hAB P hP setT)%E)
  in hLower.
rewrite hLambda
  -(@current_represented_mass_total R h2 (m+n) (i+0) AB hAB P hP) in hLower.
have hUpper := @current_cartesian_finite_mass_bound R h2 m n i 0%N A B hA hB
  S T a b hMassS hMassT.
apply/eqP; rewrite eq_le; apply/andP; split; [exact: hUpper|exact: hLower].
Qed.
End ZeroFactorMass.
