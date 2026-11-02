(** Supporting the image-cost measure in Federer (1969), 2.10.13, p. 177,
    using 2.10.8, p. 175, and 2.10.10, p. 176. Image cost is an outer
    measure before Borel regularisation. A Borel set with null image also
    has null constructed measure. it does not state these supporting
    outer-measure facts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import TopologicalBorel CaratheodoryLimitUP MetricScaleEnvelope MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum
  NonnegativeSumSupport BorelImageCoverCost BorelCoverCostUP BorelCaratheodoryMeasure
  BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization
  ExtendedRealBoundsUP MetricScaleMeasureBound MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_image_cost_is_measure]: supporting image
    outer measure zeta(S)=beta(f[S]) in 2.10.10, p. 176,
    used in 2.10.13, p. 177. This is an outer measure
    in the sense of 2.1.2, p. 53, without injectivity. *)
Lemma mapping_image_cost_is_measure (R : realType) (X Y : choiceType)
    (f : X -> Y) (beta : set Y -> \bar R) :
  is_measure beta -> is_measure (borel_image_cover_cost f beta).
Proof.
move=> hb; constructor; first by move=> A; exact: measure_nonnegative hb _.
move=> A F hF hcov.
apply: (@measure_indexed_cover R Y [the choiceType of set X] beta hb
  (f @` A) F (fun B => f @` B) hF).
move=> y [x hx <-]; have [B hB hxB] := hcov x hx.
exists B=> //; by exists x.
Qed.

(** Source for [mapping_image_cost_below_caratheodory]: supporting
    zeta<=psi comparison of 2.10.8, p. 175, for the image
    cost of 2.10.10, p. 176, on every subset, including
    non-Borel subsets needed in 2.10.13, p. 177. *)
Lemma mapping_image_cost_below_caratheodory (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R) :
  is_measure beta -> forall A,
  beta (f @` A)<=borel_caratheodory_measure (borel_image_cover_cost f beta) A.
Proof.
move=> hb A.
pose c := borel_image_cover_cost f beta.
pose nu := metric_scale_envelope (fun j : @borel_metric_sets R X => val j)
  (fun j => c (val j)) 1.
have hn := metric_scale_envelope_specification (fun j : @borel_metric_sets R X => val j)
  (fun j => c (val j)) 1.
apply: le_trans (@measure_bounded_by_metric_scale_envelope R X _ _ _ 1 nu c hn
  (mapping_image_cost_is_measure f hb) (fun j _ => lexx _) A) _.
exact: (@caratheodory_limit_upper R X _ _ _ _ (borel_caratheodory_specification c) A 1 nu lte01 hn).
Qed.

(** Source for [borel_null_image_caratheodory_null]: supporting
    converse null-set implication in 2.10.13, p. 177.
    All cells of any Borel partition of a null-image Borel
    set have zero cost; the supremum formula of 2.10.8,
    p. 175, gives zero constructed measure. *)
Lemma borel_null_image_caratheodory_null (R : realType) (X : metricType R)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R)
    (D A : set X) : is_measure beta -> countable D -> dense D ->
  borel_set A -> beta (f @` A)=0 ->
  borel_caratheodory_measure (borel_image_cover_cost f beta) A=0.
Proof.
move=> hb hD hden hA hz.
pose c := borel_image_cover_cost f beta.
have hc := borel_image_cover_cost_laws f hb.
apply/eqP; rewrite eq_le (measure_nonnegative (borel_caratheodory_is_measure hc) _) andbT.
apply: (extended_real_supremum_least
  (@borel_partition_cost_supremum_all R X c hc D A hD hden hA))=> z [H [hH ->]].
have hcell B : H B -> c B=0.
  move=> hB; apply/eqP; rewrite eq_le (measure_nonnegative hb _) andbT -hz.
  apply: (@measure_mono R Y beta hb)=> y [x hx <-].
  exists x=> //; rewrite -(borel_partition_union hH); by exists B.
by rewrite /borel_partition_cost (nonnegative_sum_zero hcell).
Qed.
