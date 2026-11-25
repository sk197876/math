(** Federer (1969), 3.1.4, p. 214: the scalar quotient parameter
    in ap D_i f is the one-dimensional Euclidean factor of 3.1.3.
    This adapter proves invariance of approximate limits under that
    existing isometric, measure-preserving identification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerNormedTopology EuclideanCoordinateMetric EuclideanOneCoordinate
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanScalarLength
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanNoncenteredVitali RealMetricBackground
  LebesgueScalarMeasure ScalarLebesgueBallContext MetricClosedBalls CenteredBallRelations
  MeasureUP MeasurePushforward PartialFunctionUP PartialFunctionPrecomposition
  MeasureApproximateLimitUP CenteredDensityTransport ApproximateLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_one_embed_isometry]: supporting scalar-line
    identification for the quotient in Federer 3.1.4, p. 214. *)
Lemma euclidean_one_embed_isometry (R : realType) (x y : real_line_metric R) :
  mdist (euclidean_one_embed x) (euclidean_one_embed y)=mdist x y.
Proof.
rewrite inner_metric_distanceE -inner_norm_topologyE euclidean_norm_one.
by rewrite /euclidean_one_embed !ffunE real_line_metric_distanceE.
Qed.

(** Source for [euclidean_one_project_isometry]: inverse scalar-line
    identification supporting Federer 3.1.4, p. 214. *)
Lemma euclidean_one_project_isometry (R : realType)
    (x y : inner_metric_space (@euclidean_inner_productP R 1)) :
  mdist (euclidean_one_project x : real_line_metric R) (euclidean_one_project y)=mdist x y.
Proof.
by rewrite -euclidean_one_embed_isometry !euclidean_one_projectK.
Qed.

(** Source for [euclidean_one_project_measure_preimage]: all-set
    measure identity supporting Federer 3.1.4, p. 214; the first-factor
    law of 2.6.5, pp. 119–120, in the inverse direction. *)
Lemma euclidean_one_project_measure_preimage (R : realType)
    (A : set (real_line_metric R)) :
  lebesgue_scalar_measure A=euclidean_lebesgue_measure 1 ((@euclidean_one_project R) @^-1` A).
Proof.
rewrite euclidean_one_measure_scalar_image.
congr (lebesgue_scalar_measure _); apply/seteqP; split=> t ht.
- exists (euclidean_one_embed t); by rewrite /= euclidean_one_embedK.
- by move: ht=> [x hx <-].
Qed.

(** Source for [euclidean_one_embed_measure_preimage]: the direct
    first-factor measure law supporting Federer 3.1.4, p. 214. *)
Lemma euclidean_one_embed_measure_preimage (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
  euclidean_lebesgue_measure 1 A=lebesgue_scalar_measure ((@euclidean_one_embed R) @^-1` A).
Proof.
change (@positive_euclidean_lebesgue_measure R 0 A=lebesgue_scalar_measure ((@euclidean_one_embed R) @^-1` A)).
by rewrite positive_euclidean_lebesgue_first /measure_pushforward.
Qed.

(** Source for [scalar_centered_ball_positive_finite]: supporting
    denominator laws for the scalar approximate limits in Federer
    3.1.4, p. 214, from the interval-length formula. *)
Lemma scalar_centered_ball_positive_finite (R : realType)
    (a : real_line_metric R) r : (0<r)%R ->
  (0<lebesgue_scalar_measure (metric_closed_ball a r))%E /\
  lebesgue_scalar_measure (metric_closed_ball a r) \is a fin_num.
Proof.
move=> hr; rewrite scalar_lebesgue_closed_ball ?ltW // fin_numE.
split; last by [].
by rewrite lte_fin mulr_gt0 // ltr0n.
Qed.

(** Source for [scalar_euclidean_approximate_limit_iff]: supporting
    exact correspondence between the scalar approximate limit in 3.1.2,
    p. 212, and the Euclidean section limits used in the opening proof
    of Federer 3.1.4, p. 214. Actual partial domains are preserved. *)
Theorem scalar_euclidean_approximate_limit_iff (R : realType)
    (Y : topologicalType) (f : partial_function (real_line_metric R) Y)
    (a : real_line_metric R) y :
  @is_measure_approximate_limit R [the metricType R of real_line_metric R] Y (@lebesgue_scalar_measure R)
    (@centered_closed_ball_relation R [the metricType R of real_line_metric R]) f a y <->
  is_measure_approximate_limit (@euclidean_lebesgue_measure R 1)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)])
    (partial_function_precompose (@euclidean_one_project R) f) (euclidean_one_embed a) y.
Proof.
have hbe (x : inner_metric_space (@euclidean_inner_productP R 1)) r (hr : (0<r)%R) :
    (0<@euclidean_lebesgue_measure R 1 (metric_closed_ball x r))%E /\
    @euclidean_lebesgue_measure R 1 (metric_closed_ball x r) \is a fin_num.
  split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
split=> hf.
- have hs : @is_measure_approximate_limit R [the metricType R of real_line_metric R] Y (@lebesgue_scalar_measure R)
      (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
      f (euclidean_one_project (euclidean_one_embed a)) y by rewrite euclidean_one_embedK.
  exact: (@centered_approximate_limit_isometric_precompose R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)]
    [the metricType R of real_line_metric R] Y
    (@euclidean_lebesgue_measure R 1) (@lebesgue_scalar_measure R)
    (@euclidean_one_project R) f (euclidean_one_embed a) y
    (euclidean_lebesgue_is_measure R 1) (lebesgue_scalar_is_measure R) hbe
    (@scalar_centered_ball_positive_finite R) (@euclidean_one_project_isometry R)
    (@euclidean_one_project_measure_preimage R) hs).
- have hh := @centered_approximate_limit_isometric_precompose R
    [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] Y
    (@lebesgue_scalar_measure R) (@euclidean_lebesgue_measure R 1)
    (@euclidean_one_embed R) (partial_function_precompose (@euclidean_one_project R) f) a y
    (lebesgue_scalar_is_measure R) (euclidean_lebesgue_is_measure R 1)
    (@scalar_centered_ball_positive_finite R) hbe (@euclidean_one_embed_isometry R)
    (@euclidean_one_embed_measure_preimage R) hf.
  apply: (@approximate_limit_graph_equivalent R [the metricType R of real_line_metric R]
    Y _ _ _ _ _ _ _ hh)=> t z.
  change (partial_function_graph f (euclidean_one_project (euclidean_one_embed t)) z <->
    partial_function_graph f t z).
  by rewrite euclidean_one_embedK.
Qed.
