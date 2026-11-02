(** Federer (1969), 3.2.39, p. 276: the
    actual tube characteristic sum of layers is bounded
    by the actual tube characteristic sum of members. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP MetricOpenThickening
  FiniteFamilyMultiplicity FiniteFamilyLayersUP FiniteFamilyCharacteristicCount
  FiniteFamilyLayerCharacteristicSum FiniteFamilyLayerTubeInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layer_tube_characteristic_bound]:
    the displayed inequality for S_(j,r) and t_(C,r) in
    Federer 3.2.39, p. 276. Every nearby layer centre
    witnesses enough nearby member sets. Counting the finite
    positive thresholds then bounds the entire characteristic
    sum at every tested point. No radius limit or measurable
    selection is assumed in this pointwise assertion. *)
Lemma finite_family_layer_tube_characteristic_bound (R:realType) (X:metricType R) (I:finType)
    (K:I->set X) (S:'I_(#|I|)->set X) (r:R)
    (chi:I->X->real_line_metric R) (sigma:'I_(#|I|)->X->real_line_metric R):
  is_finite_family_layers K S ->
  (forall i,is_characteristic_function (metric_open_thickening (K i) r) (chi i)) ->
  (forall j,is_characteristic_function (metric_open_thickening (S j) r) (sigma j)) ->
  forall z,\sum_j sigma j z<=\sum_i chi i z.
Proof.
move=>hS hChi hSigma z.
pose q:=finite_family_hit_count (fun i=>metric_open_thickening (K i) r) z.
have hPoint j:sigma j z<=if (j<q)%N then 1 else 0.
  case:(pselect (metric_open_thickening (S j) r z))=>hz.
  - rewrite (characteristic_on_set (hSigma j) hz).
    have hHit:=@finite_family_layer_tube_count_bound R X I K S r hS j z hz.
    by rewrite -/q hHit.
  - rewrite (characteristic_off_set (hSigma j) hz).
    case:(j<q)%N; [exact:ler01|exact:lexx].
have hSum:(\sum_j sigma j z<=\sum_(j:'I_(#|I|)) if (j<q)%N then 1 else 0).
  apply:ler_sum=>j _; exact:hPoint j.
apply:le_trans hSum _.
rewrite (@ordinal_threshold_characteristic_sum R #|I| q (finite_family_hit_count_bound _ z)).
rewrite (finite_family_characteristic_count hChi z); exact:lexx.
Qed.
