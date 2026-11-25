(** Supporting the projected-image argument in Federer (1969), 2.10.16, p.
    178, using the image cost of 2.10.10, p. 176. A Borel hull in the target
    pulls back under a continuous map; intersect its preimage with the
    source closure. This supporting hull is not separately asserted by
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel BorelFamilyBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic BorelImageTreeEquality
  ShrinkingBorelPartitionLevels MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleIndexedCover BorelCoverCostUP BorelCaratheodoryMeasure
  BorelCostPartitionBound CaratheodoryLimitUP ExtendedRealBoundsUP
  BorelImageCoverCost BorelImageMeasureBounds BorelRegularMeasureUP
  BorelFunctionBasic BorelFamilyBasic MetricDiameterClosure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.


(** Source for [continuous_image_cost_borel_hull]: supporting
    Borel generator replacement for 2.10.16, p. 178. The
    target Borel-regular hull of f(S) gives a source Borel
    superset C with no greater diameter or image cost. This
    works on every source set and with infinite target measures. *)
Theorem continuous_image_cost_borel_hull (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) (hr : is_borel_regular_measure beta) S :
  continuous f -> exists C, borel_set C /\ S `<=` C /\
    extended_metric_diameter C<=extended_metric_diameter S /\
    beta (f @` C)<=beta (f @` S).
Proof.
move=> hf; have [B [hSB [hB he]]] := borel_regular_cover hr (f @` S).
pose C := (f @^-1` B) `&` closure S.
have hC : borel_set C.
  apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X)).
  - exact (@borel_function_preimage X Y f (continuous_borel_function hf) B hB).
  - exact (@closed_borel_set X (closure S) (@closed_closure X S)).
exists C; split=> //; split.
- move=> x hx; split; first by apply: hSB; exists x.
  exact: subset_closure hx.
- split.
  + rewrite -(extended_metric_diameter_closure S).
    apply: extended_metric_diameter_mono; by move=> x [].
  + rewrite he; apply: (@measure_mono R Y beta hb)=> y [x [hx _] <-]; exact hx.
Qed.
