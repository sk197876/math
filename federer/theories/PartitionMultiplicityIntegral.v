(** Federer (1969), 3.2.3, p. 243: the sum of
    image measures over the univalent Borel partition equals
    the multiplicity integral, by characteristic integration
    and countable nonnegative summation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  BorelPartition MappingMultiplicity MappingPartitionMultiplicity NonnegativeSum
  TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [injective_multiplicity_integral]: the
    multiplicity integral on a single univalent piece,
    used in Federer 3.2.3, p. 243. The image
    is assumed measurable here and proved Borel in the
    Euclidean application; no finite mass is required. *)
Lemma injective_multiplicity_integral (R:realType) (X Y:choiceType)
    (f:X->Y) (B:set X) (beta:set Y->\bar R) (hb:is_measure beta):
  {in B &,injective f} -> measure_measurable beta (f @` B) ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f B y:extended_real_line R))) (beta (f @` B)).
Proof.
move=>hInj hImage.
pose s:=@CharacteristicFunction.value R Y (f @` B).
have hs:=@CharacteristicFunction.laws R Y (f @` B).
have hChar:=@measure_characteristic_integral R Y beta hb (f @` B) s hs hImage.
have hEq:=injective_mapping_multiplicity_characteristic hInj hs.
apply:(@measure_integral_graph_equivalent R Y beta _ _ _ _ hChar)=>y z.
rewrite real_total_integrand_graph.
change ((s y)%:E=z <-> @mapping_multiplicity R X Y f B y=z).
by rewrite hEq.
Qed.

(** Source for [partition_univalent_multiplicity_integral]:
    summing over H in Federer 3.2.3, p. 243.
    Its image sets may overlap: counting source fibres
    keeps the correct multiplicity in the integral. *)
Theorem partition_univalent_multiplicity_integral (R:realType) (X:topologicalType)
    (Y:choiceType) (f:X->Y) (A:set X) (H:set (set X))
    (beta:set Y->\bar R) (hb:is_measure beta):
  is_borel_partition A H -> (forall B,H B -> {in B &,injective f}) ->
  (forall B,H B -> measure_measurable beta (f @` B)) ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R)))
    (nonnegative_sum H (fun B=>beta (f @` B))).
Proof.
move=>hH hInj hImage.
have hi:=@total_countable_nonnegative_integral R Y [the choiceType of set X] beta hb H
  (fun B y=>(@mapping_multiplicity R X Y f B y:extended_real_line R))
  (fun B=>beta (f @` B)) (borel_partition_countable hH)
  (fun B hB y=>@mapping_multiplicity_nonnegative R X Y f B y)
  (fun B hB=>injective_multiplicity_integral hb (hInj B hB) (hImage B hB)).
apply:(@measure_integral_graph_equivalent R Y beta _ _ _ _ hi)=>y z.
change (nonnegative_sum H (fun B=>@mapping_multiplicity R X Y f B y)=z <->
  @mapping_multiplicity R X Y f A y=z).
by rewrite -(@mapping_partition_multiplicity R X Y f A H hH y).
Qed.
