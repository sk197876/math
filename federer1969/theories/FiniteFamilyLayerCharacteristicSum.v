(** Federer (1969), 3.2.39, p. 276: the
    characteristic sums of all layers and original images agree. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP FiniteFamilyMultiplicity
  FiniteFamilyLayersUP FiniteFamilyCharacteristicCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ordinal_threshold_characteristic_sum]: supporting
    finite ordinal count of positive multiplicity thresholds in
    Federer 3.2.39, p. 276. All thresholds up to q
    contribute one; zero thresholds and zero ambient counts remain. *)
Lemma ordinal_threshold_characteristic_sum (R:realType) N q:
  (q<=N)%N ->\sum_(j:'I_N) (if (j<q)%N then (1:R) else 0)=q%:R.
Proof.
move=>hq; rewrite -big_mkcond -(big_ord_widen N (fun _=>1:R) hq).
by rewrite sumr_const card_ord -mulr_natr mul1r.
Qed.

(** Source for [finite_family_layer_characteristic_sum]: the
    first displayed characteristic equality in Federer 3.2.39,
    p. 276. The layers have their exact independent threshold
    law and both characteristic families have their on/off laws.
    No image measurability or source dimension is needed here. *)
Lemma finite_family_layer_characteristic_sum (R:realType) (X:Type) (I:finType)
    (K:I->set X) (S:'I_(#|I|)->set X)
    (chi:I->X->real_line_metric R) (sigma:'I_(#|I|)->X->real_line_metric R):
  is_finite_family_layers K S ->
  (forall i,is_characteristic_function (K i) (chi i)) ->
  (forall j,is_characteristic_function (S j) (sigma j)) ->forall y,
    \sum_j sigma j y=\sum_i chi i y.
Proof.
move=>hS hChi hSigma y; rewrite (finite_family_characteristic_count hChi y).
have hPoint j:sigma j y=if (j<finite_family_hit_count K y)%N then 1 else 0.
  case hHit:(j<finite_family_hit_count K y)%N.
  - exact (characteristic_on_set (hSigma j) ((hS j y).2 hHit)).
  - have hNot:~S j y.
      move=>hy; by have :=(hS j y).1 hy; rewrite hHit.
    exact (characteristic_off_set (hSigma j) hNot).
rewrite (eq_bigr _ (fun j _=>hPoint j)).
exact:ordinal_threshold_characteristic_sum (finite_family_hit_count_bound K y).
Qed.
