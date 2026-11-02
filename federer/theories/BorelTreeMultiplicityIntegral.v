(** Federer (1969), 2.10.10, p. 176: Caratheodory measure with cost
    beta(f[S]) is the integral of the restricted multiplicity N(f|A,y) on
    Borel sets A. This module proves the assertion from a supplied shrinking
    Borel partition tree; the separable space supplies that tree in the
    public existence step. This is the geometric prerequisite explicitly
    cited by 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP
  ClosedCoverTreeUP CoverPartitionTreeUP PartitionHitCounts PartitionCountingLimit
  MappingMultiplicity CountingMeasure BorelCoverCostUP BorelImageCoverCost
  BorelCaratheodoryMeasure BorelPartitionCostLimits PartitionImageIntegral
  TotalIncreasingIntegralSupremum TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_tree_multiplicity_integral]:
    the complete limiting calculation in the proof of
    Federer 2.10.10, p. 176, for an
    abstract shrinking partition tree. Measurability of
    the multiplicity function is part of the integral
    conclusion; it is not assumed. *)
Theorem borel_tree_multiplicity_integral (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (E P : seq nat -> set X)
    (hE : is_closed_cover_tree E) (hP : is_cover_partition_tree E P) A :
  (forall S, borel_set S -> measure_measurable beta (f @` S)) -> borel_set A ->
  is_measure_integral beta
    (partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)))
    (borel_caratheodory_measure (borel_image_cover_cost f beta) A).
Proof.
move=> hf hA.
apply: (@total_increasing_integral_supremum R Y beta hb
  (fun n y => (@partition_hit_count R X P (mapping_fibre f A y) n : extended_real_line R))
  (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))
  (fun n => borel_partition_level_cost (borel_image_cover_cost f beta) P A n)
  (borel_caratheodory_measure (borel_image_cover_cost f beta) A)).
- move=> n y; exact (@measure_nonnegative R [the choiceType of (seq nat : Type)]
    _ (counting_measure_is_measure R _) _).
- move=> y; exact (@partition_hit_count_limit R X E P hE hP (mapping_fibre f A y)).
- move=> n; exact (@partition_image_count_integral R X Y f beta hb E P hE hP A n hf hA).
- exact (@borel_partition_cost_supremum R X (borel_image_cover_cost f beta)
    (@borel_image_cover_cost_laws R X Y f beta hb) E P hE hP A hA).
Qed.
