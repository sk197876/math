(** Supporting the projected Suslin images in Federer (1969), 2.10.16, p.
    178: the continuous-map multiplicity identity of 2.10.10, p. 176,
    extended from Borel to Suslin source sets in a complete separable metric
    space. The partition argument is unchanged; Borel image-cost hulls
    supply admissible generators. These do not state this geometric
    identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence CharacteristicFunctionUP
  CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral TotalCountableNonnegativeIntegral
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic
  ShrinkingBorelPartitionLevels PartitionHitCounts MappingMultiplicity PartitionImageCharacteristicSum
  BorelImageCoverCost BorelPartitionCostLimits TopologicalBorel BorelFamilyBasic BorelRegularMeasureUP SuslinSetUP SuslinMeasurability
  BorelImageMeasurability SuslinPartitionCostLimits SuslinImageCostHull BorelCaratheodoryMeasure
  BorelImageMeasureBounds MetricDiameter BorelClosedProjection CompleteMetricUP CountingMeasure
  PartitionCountingLimit TotalIncreasingIntegralSupremum ClosedCoverTreeSealed
  CoverPartitionTreeSealed MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [suslin_partition_image_count_integral]: the
    integral of the characteristic sum equals the sum
    of the image measures, the middle equality in the
    proof of Federer 2.10.10, p. 176.
    Supporting extension for 2.10.16, p. 178: the source
    cells may be Suslin. Infinite values and empty cells remain. *)
Lemma suslin_partition_image_count_integral (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (E P : seq nat -> set X)
    (hE : is_closed_cover_tree E) (hP : is_cover_partition_tree E P) A n :
  (forall S, is_suslin_set R S -> measure_measurable beta (f @` S)) -> is_suslin_set R A ->
  is_measure_integral beta
    (partial_function_total (fun y : Y => (@partition_hit_count R X P (mapping_fibre f A y) n : extended_real_line R)))
    (borel_partition_level_cost (borel_image_cover_cost f beta) P A n).
Proof.
move=> hf hA.
pose chi s := @CharacteristicFunction.value R Y (f @` (A `&` P s)).
have hchi s := @CharacteristicFunction.laws R Y (f @` (A `&` P s)).
have hS s : is_suslin_set R (A `&` P s) :=
  @suslin_partition_cell R X E P hE hP A s hA.
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

(** Source for [continuous_suslin_multiplicity_integral]: supporting
    extension of 2.10.10, p. 176, needed for the projected
    source images in 2.10.16, p. 178. Both the actual
    multiplicity measurability and the actual integral identity
    are proved; no finiteness or sigma-finiteness is required. *)
Theorem continuous_suslin_multiplicity_integral (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (hr : is_borel_regular_measure beta) A :
  is_complete_metric_space X -> (exists D : set X, countable D /\ dense D) ->
  hausdorff_space Y -> continuous f -> is_suslin_set R A ->
  is_measure_integral beta
    (partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)))
    (borel_caratheodory_measure (borel_image_cover_cost f beta) A).
Proof.
move=> hX hsep hY hf hA.
have himage S : is_suslin_set R S -> measure_measurable beta (f @` S).
  move=> hS; apply: (@suslin_set_measurable R Y beta hb (f @` S)).
  - move=> C hC; exact (@borel_regular_borel_measurable R Y beta hb hr C (closed_borel_set hC)).
  - exact: continuous_suslin_image hX hsep hY hf hS.
pose c := borel_image_cover_cost f beta.
have hc := @borel_image_cover_cost_laws R X Y f beta hb.
have hlow S : is_suslin_set R S -> c S<=borel_caratheodory_measure c S.
  move=> _; exact: mapping_image_cost_below_caratheodory hb S.
have hhull S : is_suslin_set R S -> exists C, borel_set C /\ S `<=` C /\
    extended_metric_diameter C<=extended_metric_diameter S /\ c C<=c S.
  move=> _; exact: continuous_image_cost_borel_hull hb hr S hf.
case: (pselect (A !=set0))=> [[x hx]|hn].
- have hnon : (@setT X) !=set0 by exists x.
  have [D [hD hden]] := hsep.
  pose E := @ClosedCoverTree.value R X D hD hden hnon.
  pose P := @CoverPartitionTree.value X E.
  have hE := @ClosedCoverTree.laws R X D hD hden hnon.
  have hP := @CoverPartitionTree.laws X E.
  apply: (@total_increasing_integral_supremum R Y beta hb
    (fun n y => (@partition_hit_count R X P (mapping_fibre f A y) n : extended_real_line R))
    (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))
    (fun n => borel_partition_level_cost c P A n) (borel_caratheodory_measure c A)).
  + move=> n y; exact (@measure_nonnegative R [the choiceType of (seq nat : Type)]
      _ (counting_measure_is_measure R _) _).
  + move=> y; exact (@partition_hit_count_limit R X E P hE hP (mapping_fibre f A y)).
  + move=> n; exact (@suslin_partition_image_count_integral R X Y f beta hb E P hE hP A n himage hA).
  + exact (@suslin_partition_cost_supremum R X c hc hlow hhull E P hE hP A hA).
- have he : A=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hn; by exists x.
  rewrite he (measure_empty (borel_caratheodory_is_measure hc)).
  apply: (measure_almost_zero_integral hb).
  apply: (@measure_almost_everywhere_mono R Y beta hb setT _ _ (measure_almost_everywhere_true hb))=> y _.
  exact: mapping_multiplicity_empty.
Qed.
