(** Federer (1969), 2.10.10, p. 176: the multiplicity integral equals the
    measure constructed from image costs on Borel sets of a separable metric
    source. The source need not be complete when image measurability is
    explicitly assumed, exactly as in the book. Completeness enters only in
    the later application of 2.2.13. Empty spaces and empty test sets are
    included. Source context: BorelTreeMultiplicityIntegral.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureConullZeroIntegral ClosedCoverTreeSealed CoverPartitionTreeSealed
  BorelImageCoverCost BorelCaratheodoryMeasure BorelTreeMultiplicityIntegral
  MappingMultiplicity TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_multiplicity_integral]: direct
    theorem of Federer 2.10.10, p. 176,
    using the actual sealed Caratheodory measure and
    actual counting multiplicity. The countable dense
    subset expresses separability; image measurability,
    not continuity or injectivity, is the printed map
    hypothesis. Measurability of multiplicity is proved. *)
Theorem borel_multiplicity_integral (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (D : set X) A :
  countable D -> dense D ->
  (forall S, borel_set S -> measure_measurable beta (f @` S)) -> borel_set A ->
  is_measure_integral beta
    (partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)))
    (borel_caratheodory_measure (borel_image_cover_cost f beta) A).
Proof.
move=> hD hden hf hA.
case: (pselect (A !=set0))=> [[x hx]|hn].
- have hX : (@setT X) !=set0 by exists x.
  pose E := @ClosedCoverTree.value R X D hD hden hX.
  pose P := @CoverPartitionTree.value X E.
  exact (@borel_tree_multiplicity_integral R X Y f beta hb E P
    (@ClosedCoverTree.laws R X D hD hden hX) (@CoverPartitionTree.laws X E) A hf hA).
- have he : A=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hn; by exists x.
  rewrite he (measure_empty (borel_caratheodory_is_measure (@borel_image_cover_cost_laws R X Y f beta hb))).
  apply: (measure_almost_zero_integral hb).
  apply: (@measure_almost_everywhere_mono R Y beta hb setT _ _ (measure_almost_everywhere_true hb))=> y _.
  exact: mapping_multiplicity_empty.
Qed.
