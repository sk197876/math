(** Supporting the arc-length image comparison in Federer (1969), 2.10.13,
    p. 177, from 2.10.11, p. 176: a map need only be nonexpanding on the set
    being measured. Restrict each covering generator to that set and discard
    empty intersections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricScaleCutoffCost MeasureUP MeasureBasic MeasureIndexedCover MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleWeightedBound MetricScaleMeasureBound
  CaratheodoryLimitUP CaratheodoryBorelRegular HausdorffLengthUP HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_length_nonexpanding_on]: supporting
    restricted image estimate for H on im s in 2.10.13, p. 177.
    No global extension of H, target completeness or measurability
    of the measured set is assumed. This is the degree-one image
    comparison underlying 2.10.11, not its multiplicity assertion. *)
Theorem hausdorff_length_nonexpanding_on (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) :
  (forall x y, A x -> A y -> (mdist (f x) (f y)<=mdist x y)%R) ->
  @hausdorff_length R Y (f @` A)<=@hausdorff_length R X A.
Proof.
move=> hf; apply: (caratheodory_limit_least (@hausdorff_length_specification R Y))=> delta tau hd ht.
have htm := metric_scale_envelope_is_measure ht
  (fun j => metric_diameter_nonnegative (extended_metric_diameter_specification (val j))).
pose q (B : set X) := tau (f @` (B `&` A)).
have hq : is_measure q.
  constructor; first by move=> B; exact: measure_nonnegative htm _.
  move=> B F hF hcov.
  apply: (@measure_indexed_cover R Y [the choiceType of set X] tau htm
    (f @` (B `&` A)) F (fun C => f @` (C `&` A)) hF).
  move=> y [x [hxB hxA] <-]; have [C hC hxC] := hcov x hxB.
  exists C=> //; exists x=> //; by split.
pose nu := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
  (fun j => extended_metric_diameter (val j)) delta.
have hn := metric_scale_envelope_specification (fun j : @nonempty_metric_sets R X => val j)
  (fun j => extended_metric_diameter (val j)) delta.
have hgen (j : @nonempty_metric_sets R X) :
    extended_metric_diameter (val j)<=delta -> q (val j)<=extended_metric_diameter (val j).
  move=> hj.
  case: (pselect (val j `&` A !=set0))=> [hne|hempty].
  - have hne' : f @` (val j `&` A) !=set0.
      have [x hx] := hne; exists (f x); by exists x.
    pose k : @nonempty_metric_sets R Y := Sub (f @` (val j `&` A)) (mem_set hne').
    have hdiam : extended_metric_diameter (val k)<=extended_metric_diameter (val j).
      apply: (metric_diameter_least (extended_metric_diameter_specification (val k))).
      + exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
      + move=> y z [x [hxj hxA] <-] [w [hwj hwA] <-].
        apply: le_trans (hf x w hxA hwA : (mdist (f x) (f w))%:E<=(mdist x w)%:E) _.
        exact: (@metric_diameter_upper R X _ _ (extended_metric_diameter_specification (val j)) x w hxj hwj).
    exact: le_trans (@metric_scale_generator_bound R Y _ _ _ delta tau k ht
      (metric_diameter_nonnegative (extended_metric_diameter_specification (val k))) (le_trans hdiam hj)) hdiam.
  - have he : val j `&` A=set0.
      apply/seteqP; split=> x hx //; exfalso; apply: hempty; by exists x.
    rewrite /q he image_set0 (measure_empty htm).
    exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
have hb := @measure_bounded_by_metric_scale_envelope R X _ _ _ delta nu q hn hq hgen A.
rewrite /q setIid in hb; apply: le_trans hb _.
exact: (@caratheodory_limit_upper R X _ _ _ _ (@hausdorff_length_specification R X) A delta nu hd hn).
Qed.
