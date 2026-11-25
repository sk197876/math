(** Federer (1969), 4.1.7, p. 356:
    characteristic functions of all ||T||-measurable
    sets satisfy the original local summability
    condition. This uses the exact intersection
    integral from Chapter 2, including infinite A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CurrentMeasurableMultiplierUP
  PartialFunctionBasic MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity
  CharacteristicFunctionUP MeasurableNormedCharacteristic CharacteristicSubsetIntegral
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_radon_locally_summable]:
    every measurable A has a locally summable
    characteristic function for Radon mu,
    supporting the original restriction in Federer
    4.1.7, p. 356. Neither A nor its
    closure is required to have finite mass. *)
Theorem characteristic_radon_locally_summable (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (A:set X) (s:X->R):
  is_characteristic_function A s ->measure_measurable mu A ->
  is_locally_summable_current_field (@scalar_absolute_value_norm R) mu s.
Proof.
move=>hs hA;split.
- exact:(@measurable_normed_characteristic R X mu hm A s hs hA).1.
- move=>K hK.
  have hKm:=@radon_compact_measurable R X mu hm hr K hK.
  have hInt:=@characteristic_subset_integral R X mu K A s hm hKm hA hs.
  have hFinite:mu (K `&` A) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm (K `&` A))).
    apply:le_lt_trans (@measure_mono R X mu hm (K `&` A) K (fun x hx=>hx.1)) _.
    exact:(@radon_compact_finite R X mu hr K hK).
  have hNorm:(fun x=>`|s x|)=s.
    apply:funext=>x;case:(pselect (A x))=>hx.
    - by rewrite (characteristic_on_set hs hx) normr1.
    - by rewrite (characteristic_off_set hs hx) normr0.
  exists (fine (mu (K `&` A)));rewrite fineK // hNorm;exact:hInt.
Qed.
