(** Federer (1969), 4.1.26, pp. 383–384:
    chi_A times the coordinate top vector
    gives exactly E^m restricted to A.
    Compare actual test actions through the original
    full-domain Lebesgue transport. The input field
    carrier and density current remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentEvaluation CurrentIntegrationCriterion
  CompactSummableMultivectors CompactSummableMultivectorDensity
  EuclideanCharacteristicCurrent EuclideanLebesgueDimensions EuclideanFullDomainMeasure
  EuclideanOpenDomainMeasure MetricDiameter CurrentMultivectorDual MultivectorDualSealed
  DistributionIntegrationRepresentationUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  RealSubsetCharacteristicIntegral CurrentBoundedCharacteristicMultivector
  FiniteExteriorPowers
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CharacteristicCurrentAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable m:nat.
Local Notation X:=(R_n R m).
Local Notation N:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation U:=(fun _:X=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior N x).
Local Notation FT:=(current_domain R m U).
Local Notation W:=(@compact_summable_multivector_space R h2 m m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 m m U hU).
Local Notation D:=(@compact_summable_multivector_current R h2 m m U hU).
Local Notation mu:=(@euclidean_open_domain_measure R m U).
Local Notation top:=(e_lambda (@coordinate_basis R m) (ord_tuple m)).
Variable A:set X.
Hypothesis hA:measure_measurable (@euclidean_lebesgue_measure R m) A.
Local Notation chi:=(@CharacteristicFunction.value R X A).
Local Notation TA:=(@euclidean_characteristic_current R h2 m A hA).

(** Source for [current_characteristic_multivector_current]:
    every actual Omega representative of chi_A
    times the coordinate orientation gives precisely
    E^m restricted to A, the substitution in
    the proof of 4.1.26, p. 384.
    Agreement is at every actual compact test. *)
Theorem current_characteristic_multivector_current (xi:W):
  (forall x:FT,value xi x=chi (set_val x)*:top)->D xi=TA.
Proof.
move=>hValues;apply:(@current_values_extensional R h2 m m U hU)=>phi.
pose k:=fun x=>pairing top (@current_test_value R h2 m U hU m phi x).
have hSubset:=@euclidean_characteristic_current_action R h2 m A hA phi.
have hIntegral:=(@real_subset_characteristic_integral R X (@euclidean_lebesgue_measure R m)
  A chi k (@current_value R h2 m U hU m TA phi)%:E
  (@CharacteristicFunction.laws R X A)).1 hSubset.
have hForward:=@euclidean_full_domain_real_integral R m
  (fun x=>chi x*k x) (@current_value R h2 m U hU m TA phi)%:E hIntegral.
pose hRepresentation:=@compact_summable_multivector_current_representation R h2 m m U hU xi.
have hOriginal:=distribution_representation_action hRepresentation phi.
have hPairing:(fun x:FT=>@MultivectorDual.evaluation R X m (value xi x)
    (@current_test_value R h2 m U hU m phi (set_val x)))=
    (fun x:FT=>chi (set_val x)*k (set_val x)).
  apply:funext=>x.
  by rewrite MultivectorDual.laws hValues /pairing linearZ.
change (is_measure_integral mu (real_total_integrand
  (fun x:FT=>@MultivectorDual.evaluation R X m (value xi x)
    (@current_test_value R h2 m U hU m phi (set_val x))))
  (@current_value R h2 m U hU m (D xi) phi)%:E) in hOriginal.
rewrite hPairing in hOriginal.
exact:EFin_inj (measure_integral_unique hOriginal hForward).
Qed.

(** Source for [current_bounded_characteristic_current_exists]:
    a bounded Lebesgue-measurable A supplies an
    actual original Omega field, its exact pointwise
    characteristic values, its actual restricted-current
    identity and its exact integral size,
    Federer 4.1.26, pp. 383–384. *)
Theorem current_bounded_characteristic_current_exists
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  exists xi:W,(forall x:FT,value xi x=chi (set_val x)*:top) /\
    D xi=TA /\
    @compact_summable_multivector_size R h2 m m U hU xi=
      fine ((@euclidean_lebesgue_measure R m) A).
Proof.
have[xi [hValues hSize]]:=@current_bounded_characteristic_multivector_exists
  R h2 m A hA hBound.
exists xi;split;first exact:hValues.
split;[exact:current_characteristic_multivector_current hValues|exact:hSize].
Qed.
End CharacteristicCurrentAgreement.
