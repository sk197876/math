(** Federer (1969), 3.1.3(2),(4), p. 213: finite unions of
    density-zero exceptional sets have density zero. This supports the
    comparison of approximate limits with upper and lower limits. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanClosedBallVolume EuclideanNoncenteredVitali MetricClosedBalls
  PartialFunctionUP MeasureUP MeasureSplit MeasureSetDensity CenteredBallRelations
  EuclideanZeroDensitySmallMass CenteredZeroDensityCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_zero_density_union]: supporting finite-union
    step for the two exceptional level sets in Federer 3.1.3(2),(4),
    p. 213. Binary subadditivity and half of each prescribed error
    suffice; neither exceptional set is required to be measurable. *)
Theorem euclidean_zero_density_union (R : realType) n
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) a :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) A) a 0 ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) B) a 0 ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) (A `|` B)) a 0.
Proof.
move=> hA hB.
apply: (@centered_small_mass_zero_density R _ _ (A `|` B) a
  (euclidean_lebesgue_is_measure R n)).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- move=> c hc.
  have hc2 : (0<c/2)%R by lra.
  have [dA [hdA hsA]] := euclidean_zero_density_small_mass hA hc2.
  have [dB [hdB hsB]] := euclidean_zero_density_small_mass hB hc2.
  exists (Num.min dA dB)%R; split; first by rewrite lt_min hdA hdB.
  move=> r hr; rewrite lt_min=> /andP[hrA hrB].
  pose C := metric_closed_ball a r.
  have hcover : (A `|` B) `&` C `<=` (A `&` C) `|` (B `&` C).
    by move=> x [[hx|hx] hxc]; [left|right]; split.
  have hmass := @measure_binary_cover R _ _ (euclidean_lebesgue_is_measure R n)
    _ _ _ hcover.
  have hsum := lteD (hsA r hr hrA) (hsB r hr hrB).
  have he : (c/2)%R%:E*euclidean_lebesgue_measure n C+
      (c/2)%R%:E*euclidean_lebesgue_measure n C=
      c%:E*euclidean_lebesgue_measure n C.
    rewrite /C (euclidean_closed_ball_normalized_volume a (ltW hr)) -!EFinM -EFinD.
    congr (_%:E); lra.
  by apply: le_lt_trans hmass _; rewrite -he.
Qed.
