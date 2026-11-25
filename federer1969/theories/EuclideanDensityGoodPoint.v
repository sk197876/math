(** Federer (1969), 3.1.2, p. 212: a small exceptional mass cannot
    cover a smaller ball contained in the ball used to measure density.
    This isolates the geometric step in uniqueness of the approximate
    differential and retains outer measures of arbitrary exceptional sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanClosedBallVolume EuclideanBallVolume MetricClosedBalls
  PartialFunctionUP MeasureUP MeasureBasic MeasureSetDensity MeasureSplit
  CenteredBallRelations EuclideanZeroDensitySmallMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_two_small_sets_good_point]: supporting the
    choice of v in Federer 3.1.2, p. 212. Two exceptional sets each of
    mass less than half the smaller ball's mass leave a point outside
    both. This version works at the original base point without translating
    a density limit. *)
Lemma euclidean_two_small_sets_good_point (R : realType) n
    (A B : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : inner_metric_space (@euclidean_inner_productP R n)) (r t : R) :
  (0<r)%R -> (0<t)%R ->
  metric_closed_ball b (t*r)%R `<=` metric_closed_ball a r ->
  euclidean_lebesgue_measure n (A `&` metric_closed_ball a r) <
    (t^+n/2)%R%:E * euclidean_lebesgue_measure n (metric_closed_ball a r) ->
  euclidean_lebesgue_measure n (B `&` metric_closed_ball a r) <
    (t^+n/2)%R%:E * euclidean_lebesgue_measure n (metric_closed_ball a r) ->
  exists v, metric_closed_ball b (t*r)%R v /\ ~ A v /\ ~ B v.
Proof.
move=> hr ht hsub hA hB; apply: contrapT=> hn.
have hcover : metric_closed_ball b (t*r)%R `<=`
    (A `&` metric_closed_ball a r) `|` (B `&` metric_closed_ball a r).
  move=> v hv; have hvr := hsub v hv.
  have [hvA|hvA] := pselect (A v); first by left; split.
  right; split=> //; apply: contrapT=> hvB; apply: hn.
  by exists v; split=> //; split.
have hm := @measure_binary_cover R _ _ (euclidean_lebesgue_is_measure R n) _ _ _ hcover.
have hs := lteD hA hB.
have htr : (0<t*r)%R by rewrite mulr_gt0.
rewrite !euclidean_closed_ball_normalized_volume ?ltW // -!EFinM -EFinD in hs.
have he : ((t^+n/2)*(euclidean_unit_ball_volume R n*r^+n)+
    (t^+n/2)*(euclidean_unit_ball_volume R n*r^+n)=
    euclidean_unit_ball_volume R n*(t*r)^+n)%R.
  rewrite -mulrDl -splitr exprMn; by rewrite mulrCA.
rewrite he in hs.
rewrite (euclidean_closed_ball_normalized_volume b (ltW htr)) in hm.
by have := le_lt_trans hm hs; rewrite ltxx.
Qed.

(** Source for [euclidean_zero_density_good_point]: the point selection
    used for uniqueness in Federer 3.1.2, p. 212. Given two density-zero
    exceptional sets, every sufficiently small containing ball permits
    the selection in any included ball with a prescribed positive radius
    ratio. No measurable representative of either exceptional set is chosen. *)
Theorem euclidean_zero_density_good_point (R : realType) n
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) a :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) A) a 0 ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) B) a 0 ->
  forall t : R, (0<t)%R -> exists d : R, (0<d)%R /\ forall r b,
    (0<r)%R -> (r<d)%R ->
    metric_closed_ball b (t*r)%R `<=` metric_closed_ball a r ->
    exists v, metric_closed_ball b (t*r)%R v /\ ~ A v /\ ~ B v.
Proof.
move=> hA hB t ht.
have hc : (0<t^+n/2)%R by rewrite divr_gt0 ?exprn_gt0 // ltr0n.
have [dA [hdA hsmallA]] := euclidean_zero_density_small_mass hA hc.
have [dB [hdB hsmallB]] := euclidean_zero_density_small_mass hB hc.
exists (Num.min dA dB)%R; split; first by rewrite lt_min hdA hdB.
move=> r b hr hrd hsub.
move: hrd; rewrite lt_min=> /andP [hrA hrB].
exact: euclidean_two_small_sets_good_point hr ht hsub (hsmallA _ hr hrA) (hsmallB _ hr hrB).
Qed.
