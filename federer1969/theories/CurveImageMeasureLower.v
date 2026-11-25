(** Federer (1969), 2.10.13, p. 177, first proof paragraph: connected
    interval images give the lower bound of variation by the image-cost
    Caratheodory measure. This is exactly the use of 2.10.12, p. 176, and
    the Borel construction of 2.10.8, p. 175. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normed_module num_normedtype.
From Federer Require Import IntervalBumpFunctions ExtendedRealBounds RealMetricBackground CurveVariationUP StieltjesContinuityPoints
  StieltjesContinuousIntegrator MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  BorelImageCoverCost BorelCoverCostUP BorelCaratheodoryMeasure MetricScaleEnvelopeUP
  MetricScaleWeightedBound CaratheodoryLimitUP HausdorffLength HausdorffLengthCompatibility
  HausdorffMeasure HausdorffCountableNull MetricDiameterUP MetricDiameter MetricDiameterMaps ConnectedHausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_image_measure_singleton_null]: supporting
    omission of partition endpoints in 2.10.13, p. 177.
    A singleton has singleton image and zero H1 cost at
    every positive source cutoff, so also zero final measure. *)
Lemma curve_image_measure_singleton_null (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) :
  @borel_caratheodory_measure R [the metricType R of real_line_metric R] (borel_image_cover_cost g (@hausdorff_length R Y)) [set x]=0.
Proof.
pose c := borel_image_cover_cost g (@hausdorff_length R Y).
have hc := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
apply/eqP; rewrite eq_le (measure_nonnegative (@borel_caratheodory_is_measure R [the metricType R of real_line_metric R] c hc) _) andbT.
apply: (caratheodory_limit_least (@borel_caratheodory_specification R [the metricType R of real_line_metric R] c))=> delta nu hd hn.
have hx : borel_set [set (x : real_line_metric R)].
  apply: closed_borel_set; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
pose j : @borel_metric_sets R [the metricType R of real_line_metric R] :=
  Sub [set x] (mem_set hx).
have hcost : c (val j)=0.
  rewrite /c /borel_image_cover_cost image_set1 -hausdorff_measure_one_length.
  exact: hausdorff_positive_degree_singleton_zero (ltn0Sn 0).
have hsize : extended_metric_diameter (val j)<=delta.
  rewrite /j /= extended_metric_diameter_singleton; exact: ltW hd.
have hc0 : 0<=c (val j) by rewrite hcost.
have hb := @metric_scale_generator_bound R [the metricType R of real_line_metric R]
  (@borel_metric_sets R [the metricType R of real_line_metric R])
  (fun j => val j) (fun j => c (val j)) delta nu j hn hc0 hsize.
by rewrite hcost in hb.
Qed.

(** Source for [continuous_curve_image_measure_increment_bound]:
    direct distance/connected-image estimate in 2.10.13, p. 177,
    from 2.10.12, p. 176. Null endpoints allow the open
    interval used in Federer's disjoint partition sum. *)
Lemma continuous_curve_image_measure_increment_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<=b)%R ->
  (mdist (g a) (g b))%:E<=
    @borel_caratheodory_measure R [the metricType R of real_line_metric R] (borel_image_cover_cost g (@hausdorff_length R Y)) `]a,b[.
Proof.
move=> hg hab.
pose c := borel_image_cover_cost g (@hausdorff_length R Y).
pose mu := @borel_caratheodory_measure R [the metricType R of real_line_metric R] c.
have hc := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] c hc.
have hconn : connected (g @` (`[a,b] : set (real_line_metric R))).
  have hI : connected (`[a,b] : set (real_line_metric R)).
    apply/(proj2 (connected_intervalP _))=> x y hx hy z /andP[hxz hzy].
    move: hx hy; rewrite /= !in_itv /= => /andP[hax _] /andP[_ hyb].
    by rewrite (le_trans hax hxz) (le_trans hzy hyb).
  exact: connected_continuous_connected hI (continuous_subspaceT hg).
have ha : (g @` `[a,b]) (g a) by exists a=> //; rewrite /= in_itv /= lexx hab.
have hb : (g @` `[a,b]) (g b) by exists b=> //; rewrite /= in_itv /= hab lexx.
have hdist := @metric_diameter_upper R Y _ _
  (extended_metric_diameter_specification (g @` `[a,b])) (g a) (g b) ha hb.
have hlength := connected_hausdorff_length_diameter_bound hconn.
have hcost := @borel_caratheodory_cost_bound R [the metricType R of real_line_metric R]
  c hc `[a,b] (closed_borel_set (@segment_closed_real R a b)).
have he := @measure_segment_open_interval R mu a b hm
  (@curve_image_measure_singleton_null R Y g a) (@curve_image_measure_singleton_null R Y g b).
rewrite /mu in he; rewrite he in hcost.
exact: le_trans (le_trans hdist hlength) hcost.
Qed.

(** Source for [metric_chain_sum_open_interval_bound]: supporting
    finite-sum step of 2.10.13, p. 177. If every endpoint
    distance is bounded by the measure of the intervening open
    interval, a sorted chain sum is bounded by its whole interval.
    This uses only measurable disjoint open intervals and includes
    repeated partition terms. *)
Lemma metric_chain_sum_open_interval_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (mu : set R -> \bar R) (s : seq R) :
  is_measure mu -> (forall a b, measure_measurable mu `]a,b[) ->
  (forall a b, (a<=b)%R -> (mdist (g a) (g b))%:E<=mu `]a,b[) ->
  sorted <=%O s -> (chain_sum g s)%:E<=mu `]head 0%R s,last 0%R s[.
Proof.
move=> hm hmeas hinc; elim: s=> [|t [|u rest] ih] hs.
- exact: measure_nonnegative hm _.
- exact: measure_nonnegative hm _.
have /andP[htu hs'] := hs.
have hul : (u<=last u rest)%R.
  by have := @sorted_le_last R (u :: rest) 0%R u hs' (mem_head u rest); rewrite /=.
have hih := ih hs'; rewrite [head _ _]/= [last _ _]/= in hih.
rewrite chain_sum_cons EFinD [head _ _]/= [last _ _]/=.
apply: le_trans (leeD (hinc t u htu) hih) _.
exact: open_interval_superadditive hm (hmeas t u) htu hul.
Qed.

(** Source for [continuous_curve_variation_image_measure_lower]:
    direct first inequality in the proof of 2.10.13, p. 177.
    Taking the supremum over all variation partitions includes
    infinite variation; no bounded-variation hypothesis is added. *)
Theorem continuous_curve_variation_image_measure_lower (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) ->
  curve_variation g a b<=
    @borel_caratheodory_measure R [the metricType R of real_line_metric R] (borel_image_cover_cost g (@hausdorff_length R Y)) `]a,b[.
Proof.
move=> hg.
pose c := borel_image_cover_cost g (@hausdorff_length R Y).
have hc := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] c hc.
have hr := @borel_caratheodory_borel_regular R [the metricType R of real_line_metric R] c hc.
apply: extended_real_sup_least=> z [s [hs ->]].
have [hsort [hn [hh hl]]] := hs.
have hh0 : head 0%R s=a by case: s hn hh hl hsort {hs}=> // p s' hn hh hl hsort.
have hl0 : last 0%R s=b by case: s hn hh hl hsort {hs hh0}=> // p s' hn hh hl hsort.
have hmeas u v : measure_measurable (@borel_caratheodory_measure R [the metricType R of real_line_metric R] c) `]u,v[.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R] _ hm hr).
  apply: open_borel_set; exact: interval_open.
have hb := @metric_chain_sum_open_interval_bound R Y g
  (@borel_caratheodory_measure R [the metricType R of real_line_metric R] c) s hm hmeas
  (fun u v huv => @continuous_curve_image_measure_increment_bound R Y g u v hg huv) hsort.
by rewrite hh0 hl0 in hb.
Qed.
