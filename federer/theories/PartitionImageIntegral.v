(** Integration of the partition characteristic sum in Federer (1969),
    2.10.10, p. 176, using 2.4.5, p. 83, and 2.4.8, p. 84. The sum is
    countable even when the original fibre is not. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence CharacteristicFunctionUP
  CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral TotalCountableNonnegativeIntegral
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic
  ShrinkingBorelPartitionLevels PartitionHitCounts MappingMultiplicity PartitionImageCharacteristicSum
  BorelImageCoverCost BorelPartitionCostLimits TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partition_image_count_integral]: the
    integral of the characteristic sum equals the sum
    of the image measures, the middle equality in the
    proof of Federer 2.10.10, p. 176.
    Infinite measures and empty cells are allowed. *)
Lemma partition_image_count_integral (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (E P : seq nat -> set X)
    (hE : is_closed_cover_tree E) (hP : is_cover_partition_tree E P) A n :
  (forall S, borel_set S -> measure_measurable beta (f @` S)) -> borel_set A ->
  is_measure_integral beta
    (partial_function_total (fun y : Y => (@partition_hit_count R X P (mapping_fibre f A y) n : extended_real_line R)))
    (borel_partition_level_cost (borel_image_cover_cost f beta) P A n).
Proof.
move=> hf hA.
pose chi s := @CharacteristicFunction.value R Y (f @` (A `&` P s)).
have hchi s := @CharacteristicFunction.laws R Y (f @` (A `&` P s)).
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X))=> //.
  exact (@cover_partition_borel R X E P hE hP s).
have hi := @total_countable_nonnegative_integral R Y [the choiceType of (seq nat : Type)]
  beta hb [set s | size s=n] (fun s y => ((chi s y)%:E : extended_real_line R))
  (fun s => beta (f @` (A `&` P s))) (cover_partition_level_countable n)
  (fun s _ y => characteristic_extended_nonnegative (hchi s) y)
  (fun s _ => @measure_total_characteristic_integral R Y beta hb
    (f @` (A `&` P s)) (chi s) (hchi s) (hf _ (hS s))).
apply: (@measure_integral_graph_equivalent R Y beta _ _ _ _ hi).
move=> y z; change (nonnegative_sum [set s | size s=n] (fun s => (chi s y)%:E)=z <->
  @partition_hit_count R X P (mapping_fibre f A y) n=z).
by rewrite /chi partition_image_characteristic_sum.
Qed.
