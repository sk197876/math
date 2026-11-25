(** Federer (1969), 4.1.26, p. 384:
    E^m restricted to A plus E^m restricted
    to its complement is E^m. Prove the
    original identity on every actual test using
    the preceding characteristic and integral laws.
    No boundary regularity or boundedness is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation
  EuclideanFundamentalCurrent EuclideanCharacteristicCurrent EuclideanLebesgueDimensions
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP
  SummableRealArithmetic RealSubsetCharacteristicIntegral
  Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_characteristic_current_complement_sum]:
    the original complementary Euclidean restrictions
    sum to E^m, giving the first displayed
    boundary identity in 4.1.26, p. 384.
    Both measurable-set witnesses may be arbitrary. *)
Theorem euclidean_characteristic_current_complement_sum
    (R:realType) (h2:(1+1:R)!=0) m
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hAc:measure_measurable (@euclidean_lebesgue_measure R m) (~` A)):
  @euclidean_characteristic_current R h2 m A hA+
    @euclidean_characteristic_current R h2 m (~` A) hAc=
      @euclidean_fundamental_current R h2 m.
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose top:=e_lambda (@coordinate_basis R m) (ord_tuple m).
pose TA:=@euclidean_characteristic_current R h2 m A hA.
pose TC:=@euclidean_characteristic_current R h2 m (~` A) hAc.
pose s:=@CharacteristicFunction.value R X A.
pose t:=@CharacteristicFunction.value R X (~` A).
pose hs:=@CharacteristicFunction.laws R X A.
pose ht:=@CharacteristicFunction.laws R X (~` A).
apply:(@current_values_extensional R h2 m m U hU)=>phi.
pose k:=fun x=>pairing top (@current_test_value R h2 m U hU m phi x).
pose a:=@current_value R h2 m U hU m TA phi.
pose b:=@current_value R h2 m U hU m TC phi.
have hIA:=(@real_subset_characteristic_integral R X (@euclidean_lebesgue_measure R m)
  A s k a%:E hs).1 (@euclidean_characteristic_current_action R h2 m A hA phi).
have hIC:=(@real_subset_characteristic_integral R X (@euclidean_lebesgue_measure R m)
  (~` A) t k b%:E ht).1 (@euclidean_characteristic_current_action R h2 m (~` A) hAc phi).
have hSum:=@real_total_integral_add R X (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) (fun x=>s x*k x) (fun x=>t x*k x) a b hIA hIC.
have hValues:(fun x=>s x*k x+t x*k x)=k.
  apply:funext=>x;rewrite /s /t;case:(pselect (A x))=>hx.
  - by rewrite (characteristic_on_set hs hx)
      (characteristic_off_set ht (fun h=>h hx)) mul1r mul0r addr0.
  - by rewrite (characteristic_off_set hs hx)
      (characteristic_on_set ht hx) mul0r mul1r add0r.
rewrite hValues in hSum.
have hE:=@euclidean_fundamental_current_action R h2 m phi.
have hEqual:=EFin_inj (measure_integral_unique hSum hE).
rewrite (linD (hom_linear (@current_value R h2 m U hU m))) hom_addE.
exact:hEqual.
Qed.
