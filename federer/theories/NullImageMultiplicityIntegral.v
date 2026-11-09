(** Federer (1969), 3.3.20, p. 306:
    null coordinate images have zero original multiplicity integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MappingMultiplicity CountingMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_image_original_multiplicity_integral]:
    supporting application of 3.2.27 in 3.3.20,
    p. 306. The actual multiplicity is zero
    outside the original image. Nullity of that image
    gives integral zero without source measurability or
    finiteness of fibres. *)
Lemma null_image_original_multiplicity_integral (R:realType) (X Y:choiceType)
    (mu:set Y->\bar R) (f:X->Y) (W:set X):
  is_measure mu ->mu (f @` W)=0 ->
  is_measure_integral mu (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f W y:extended_real_line R))) 0.
Proof.
move=>hMu hNull;apply:(@measure_almost_zero_integral R Y mu hMu _).
apply:(@measure_null_subset R Y mu hMu _ (f @` W) _ hNull).
move=>y hy.
case:(pselect ((f @` W) y))=>[//|hNo].
exfalso;apply:hy.
change (@mapping_multiplicity R X Y f W y=0).
have hEmpty:mapping_fibre f W y=set0.
  apply/seteqP;split=>x;last by [].
  move=>[hx hValue];apply:hNo;by exists x.
rewrite /mapping_multiplicity hEmpty;exact:measure_empty (counting_measure_is_measure R X).
Qed.
