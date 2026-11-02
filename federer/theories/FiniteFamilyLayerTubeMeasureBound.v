(** Federer (1969), 3.2.39, p. 276: integrate
    the actual finite layer tube characteristic comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureIntegralUP MeasureIntegral
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureExtendedCharacteristicIntegral TotalFiniteNonnegativeIntegral
  FiniteNonnegativeIntegralComparison FiniteFamilyLayersUP FiniteFamilyLayerTubeCharacteristicBound
  MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layer_tube_measure_bound]: the
    integration of the tube characteristic inequality in Federer
    3.2.39, p. 276. Actual finite nonnegative integrals and
    the proved pointwise count give the mass inequality. Only
    measurability of open sets is used, so the original family
    members need not be measurable. Infinite tube masses and
    empty finite families remain. *)
Lemma finite_family_layer_tube_measure_bound (R:realType) (X:metricType R) (I:finType)
    (mu:set X->\bar R) (K:I->set X) (S:'I_(#|I|)->set X) (r:R):
  is_measure mu ->(forall U:set X,open U ->measure_measurable mu U) ->
  is_finite_family_layers K S ->
  ((\sum_j mu (metric_open_thickening (S j) r))<=
    (\sum_i mu (metric_open_thickening (K i) r)))%E.
Proof.
move=>hm hOpen hS.
pose chi i:=@CharacteristicFunction.value R X (metric_open_thickening (K i) r).
pose sigma j:=@CharacteristicFunction.value R X (metric_open_thickening (S j) r).
have hChi i:=@CharacteristicFunction.laws R X (metric_open_thickening (K i) r).
have hSigma j:=@CharacteristicFunction.laws R X (metric_open_thickening (S j) r).
have hKI i:=@measure_total_characteristic_integral R X mu hm _ (chi i) (hChi i)
  (hOpen _ (metric_open_thickening_open (K i) r)).
have hSI j:=@measure_total_characteristic_integral R X mu hm _ (sigma j) (hSigma j)
  (hOpen _ (metric_open_thickening_open (S j) r)).
pose F (z:X):extended_real_line R:=(\sum_j (sigma j z)%:E)%E.
have hIntegral:=@total_finite_nonnegative_integral R X [the finType of 'I_(#|I|)] mu hm
  (fun j z=>((sigma j z)%:E:extended_real_line R)) (fun j=>mu (metric_open_thickening (S j) r))
  (fun j z=>characteristic_extended_nonnegative (hSigma j) z) hSI.
have hPoint z:(F z<=\sum_i (chi i z)%:E)%E.
  rewrite /F !sumEFin lee_fin.
  exact:(@finite_family_layer_tube_characteristic_bound R X I K S r chi sigma hS hChi hSigma z).
have hCompare:=@finite_nonnegative_integral_comparison R X I mu hm F
  (fun i z=>((chi i z)%:E:extended_real_line R)) (fun i=>mu (metric_open_thickening (K i) r))
  (fun i z=>characteristic_extended_nonnegative (hChi i) z) hKI hPoint.
have hValue:=measure_upper_integral_unique (measure_upper_integral_specification mu (partial_function_total F)) hIntegral.2.1.
by rewrite hValue in hCompare.
Qed.
