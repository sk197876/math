(** Federer (1969), 4.1.21, p. 378: in the second
    corollary, the original measurable restriction of a flat
    current to a compact set is flat, by 4.1.17,
    p. 374. The characteristic zero-form belongs to the
    actual variation L1 space because Radon measure is finite
    on compact sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ScalarCoefficients RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP CurrentMeasurableMultiplierUP
  CurrentMeasurableProducts CurrentMeasurableRestriction
  CurrentCharacteristicContraction CurrentVariationFormLone
  FlatCurrentsUP FlatCurrentMeasurableContraction
  CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP RadonMeasureUP RadonBorelRegularity MeasureVectorIntegralUP
  MeasureVectorCharacteristicIntegral MeasureLpMembershipUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatCompactMeasurableRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT:=(current_domain R n U).
Local Notation Y:=(A_m X R^o 0%N).
Local Notation NY:=(@current_form_comass R h2 n 0%N).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n 0%N).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hBase:=(normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Local Notation hm:=(distribution_representation_measure hBase).
Local Notation hr:=(distribution_representation_radon hBase).
Variable A:set UT.
Hypothesis hA:compact A.

(** Source for [current_flat_compact_measurable_restriction]:
    the compact characteristic contraction used in the second
    proof of 4.1.21, p. 378. The restriction is the
    already defined actual current operation. Its flat compact
    index is inherited from T by 4.1.17, p. 374;
    neither normality nor finite total mass of T is needed. *)
Theorem current_flat_compact_measurable_restriction
    (hMeasurable:measure_measurable mu A):
  @is_flat_current R h2 n m U hU T->
  @is_flat_current R h2 n m U hU
    (@current_measurable_restriction R h2 n m U hU T hT A hMeasurable).
Proof.
move=>[K hFlatK].
pose chi:=@CharacteristicFunction.value R UT A.
pose hChi:=@CharacteristicFunction.laws R UT A.
have hFinite:(mu A< +oo)%E:=@radon_compact_finite R UT mu hr A hA.
have hNumber:mu A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm A));exact:hFinite.
pose b:=fine (mu A).
have hMass:mu A=b%:E by rewrite /b fineK.
pose y:Y:=@zero_form R X R^o 1.
pose phi:=fun x:UT=>chi x*:y.
have hLone:is_measure_lp_function mu 1
    (partial_function_total (fun x=>(phi x:real_norm_metric_space hNY))).
  exact:(@measure_vector_characteristic_integral R UT Y NY hNY
    mu hm A chi b y hChi hMeasurable hMass).1.
pose hLocal:=@current_variation_form_lone_locally_summable
  R h2 n m 0%N U hU T hT phi hLone.
have hValues x:phi x=@zero_form R X R^o (chi x).
  rewrite /phi /y -linearZ.
  change (@zero_form R X R^o (chi x*1)=@zero_form R X R^o (chi x)).
  by rewrite mulr1.
have hRestriction:=@current_characteristic_contraction_restriction
  R h2 n m U hU T hT A hMeasurable phi hLocal hValues.
exists K;rewrite -hRestriction.
exact:(@flat_current_measurable_contraction_supported
  R h2 n 0%N m U hU K T hT phi hLocal hFlatK hLone).
Qed.
End CurrentFlatCompactMeasurableRestriction.
