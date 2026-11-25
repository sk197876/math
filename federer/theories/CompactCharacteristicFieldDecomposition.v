(** Federer (1969), 4.1.23, p. 379:
    replacing a step value by its attained
    simple decomposition leaves both the actual field
    and the exact total L1 cost unchanged.
    Null cells and zero summands are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP
  CharacteristicFunctionUP CharacteristicFunctionSealed
  CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldExtensionality CompactSummableFiniteCells
  CompactCharacteristicSummableField CompactSummableExactFiniteCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_characteristic_field_decomposition]:
    the mass-optimal decomposition of every
    constant step value in Federer 4.1.23,
    p. 379, becomes an actual finite
    sum of compact L1 fields with equal
    total cost. This supporting law states the
    algebraic and norm identities explicitly; the
    multivector consumer supplies the proved attained
    decomposition of 1.8.1. *)
Theorem compact_characteristic_field_decomposition (R : realType)
    (X : topologicalType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) (mu : set X -> \bar R) (hm : is_measure mu)
    (K A : set X) (hK : compact K) (hA : measure_measurable mu A)
    (hFinite : (mu A< +oo)%E) (hAK : A `<=` K)
    (I : finType) (z : V) (u : I -> V)
    (hSum : z=\sum_i u i) (hCost : N z=\sum_i N (u i))
    (f : @CompactSummableField.space R X V N hN mu hm)
    (hValue : forall x, @compact_summable_field_value R X V N hN mu hm f x=
      @CharacteristicFunction.value R X A x*:z) :
  exists g : I -> @CompactSummableField.space R X V N hN mu hm,
    (forall i x, @compact_summable_field_value R X V N hN mu hm (g i) x=
      @CharacteristicFunction.value R X A x*:u i) /\
    (forall i, (@compact_summable_field_size R X V N hN mu hm (g i))%:E=
      ((N (u i))%:E*mu A)%E) /\
    f=\sum_i g i /\
    @compact_summable_field_size R X V N hN mu hm f=
      \sum_i @compact_summable_field_size R X V N hN mu hm (g i).
Proof.
pose W := @CompactSummableField.space R X V N hN mu hm.
pose value := @compact_summable_field_value R X V N hN mu hm.
pose size := @compact_summable_field_size R X V N hN mu hm.
pose chi := @CharacteristicFunction.value R X A.
pose hChi := @CharacteristicFunction.laws R X A.
have hPieces i : exists g : W,
    (forall x, value g x=chi x*:u i) /\
    (size g)%:E=((N (u i))%:E*mu A)%E /\
    forall x, ~K x -> value g x=0.
  exact: (@compact_characteristic_summable_field_exists R X V N hN mu hm
    A hA hFinite K hK hAK (u i)).
have [g hG] := choice hPieces.
have hField : f=\sum_i g i.
  apply: (@compact_summable_field_value_injective R X V N hN mu hm).
  apply: funext=> x; rewrite compact_summable_field_value_finite_sum
    (@hValue x) hSum scaler_sumr.
  apply: eq_bigr=> i _; symmetry; exact: (hG i).1.
have hNorm x : N (value f x)=\sum_i N (value (g i) x).
  have hLocalValue : value f x=chi x*:z := @hValue x.
  rewrite hLocalValue.
  under eq_bigr do rewrite (hG _).1.
  case: (pselect (A x))=> hx.
  - have hChiOn : chi x = 1 := characteristic_on_set hChi hx.
    rewrite hChiOn scale1r.
    under eq_bigr do rewrite scale1r.
    exact: hCost.
  - have hChiOff : chi x = 0 := characteristic_off_set hChi hx.
    rewrite hChiOff scale0r (real_seminorm_zero hN.1).
    symmetry; apply: big1=> i _; by rewrite scale0r (real_seminorm_zero hN.1).
exists g; split; first by move=> i x; exact: (hG i).1.
split; first by move=> i; exact: (hG i).2.1.
split; first exact: hField.
exact: (@compact_summable_exact_finite_cost R X V N hN mu hm I f g hNorm).
Qed.
