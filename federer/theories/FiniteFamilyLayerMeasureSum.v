(** Federer (1969), 3.2.39, p. 276: integrate
    the exact finite layer characteristic identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureExtendedCharacteristicIntegral TotalFiniteNonnegativeIntegral
  FiniteFamilyLayersUP FiniteFamilyLayerCharacteristicSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layer_measure_sum]: the second
    equality in the first display on p. 276 of Federer
    3.2.39. Finite nonnegative characteristic integration and
    the actual layer sum prove the equality of mass sums.
    The index family may be empty and the measure values
    may be infinite; no disjointness of the original sets
    or global finiteness of the measure is needed. *)
Lemma finite_family_layer_measure_sum (R:realType) (X:choiceType) (I:finType)
    (mu:set X->\bar R) (K:I->set X) (S:'I_(#|I|)->set X):
  is_measure mu ->is_finite_family_layers K S ->
  (forall i,measure_measurable mu (K i)) ->(forall j,measure_measurable mu (S j)) ->
  (\sum_j mu (S j))%E=(\sum_i mu (K i))%E.
Proof.
move=>hm hS hKMeas hSMeas.
pose chi i:=@CharacteristicFunction.value R X (K i).
pose sigma j:=@CharacteristicFunction.value R X (S j).
have hChi i:=@CharacteristicFunction.laws R X (K i).
have hSigma j:=@CharacteristicFunction.laws R X (S j).
have hKI i:=@measure_total_characteristic_integral R X mu hm (K i) (chi i) (hChi i) (hKMeas i).
have hSI j:=@measure_total_characteristic_integral R X mu hm (S j) (sigma j) (hSigma j) (hSMeas j).
have hSumK:=@total_finite_nonnegative_integral R X I mu hm
  (fun i x=>((chi i x)%:E:extended_real_line R)) (fun i=>mu (K i))
  (fun i x=>characteristic_extended_nonnegative (hChi i) x) hKI.
have hSumS:=@total_finite_nonnegative_integral R X [the finType of 'I_(#|I|)] mu hm
  (fun j x=>((sigma j x)%:E:extended_real_line R)) (fun j=>mu (S j))
  (fun j x=>characteristic_extended_nonnegative (hSigma j) x) hSI.
have hEqual:(fun x:X=>(\sum_j (sigma j x)%:E:extended_real_line R))=
    (fun x:X=>(\sum_i (chi i x)%:E:extended_real_line R)).
  apply:funext=>x; rewrite !sumEFin.
  by rewrite (@finite_family_layer_characteristic_sum R X I K S chi sigma hS hChi hSigma x).
rewrite hEqual in hSumS.
exact:measure_integral_unique hSumS hSumK.
Qed.
