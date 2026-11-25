(** Federer (1969), 4.1.2, p. 347: the
    Lebesgue-point means are the original norm-error
    integrals divided by actual Euclidean ball volumes.
    All local integrability and positive denominator
    premises are discharged from the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  MetricClosedBalls TopologicalBorel SmoothCompactSet EuclideanLebesgueDimensions EuclideanClosedBallGrowth
  EuclideanDistributionMeasureContext EuclideanNormClosedBalls LocallyIntegrableVectorFieldUP LocalVectorDistanceIntegral
  PartialFunctionBasic MeasureUP MeasureSubsetIntegral MeasurableDistanceTo MeasureLebesgueSet LebesguePointBallMeans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section EuclideanLocalDistanceMeans.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation C := (@euclidean_closed_unit_volume R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable f:X->Y.
Hypothesis hField:@is_locally_integrable_vector_field R X Y N NY hN hNY mu f.

(** Source for [euclidean_locally_integrable_ball_distance]: each
    original compact-ball norm error has a finite
    actual integral, supporting Federer 4.1.2, p. 347. *)
Theorem euclidean_locally_integrable_ball_distance (a:T) (r:R):
  0<r ->exists J:R,is_measure_subset_integral mu (metric_closed_ball a r)
    (partial_distance_to (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) (f a)) J%:E.
Proof.
move=>hr.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  (metric_closed_ball a r) (fun _ _=>Logic.I) (@euclidean_norm_closed_ball_compact R n a r).
have hMeas:measure_measurable mu (metric_closed_ball a r).
  exact:(@euclidean_distribution_measure_borel R n _ (@closed_borel_set [the topologicalType of T] (metric_closed_ball a r) (@metric_closed_ball_closed R [the metricType R of T] a r))).
exact:(@locally_integrable_vector_compact_distance R X Y N NY hN hNY mu
  (euclidean_lebesgue_is_measure R n) f K (C*r^+n) (f a) hField hMeas
  (@euclidean_norm_closed_ball_measure R n a r hr)).
Qed.

(** Source for [euclidean_lebesgue_point_ball_mean_small]: the
    exact mean limit used in the smoothing display
    of Federer 4.1.2, p. 347. It
    applies to every original Lebesgue point,
    rather than merely an almost-everywhere subset. *)
Theorem euclidean_lebesgue_point_ball_mean_small (V:T->set T->Prop) (a:T):
  (forall r:R,0<r ->V a (metric_closed_ball a r)) ->
  @measure_lebesgue_set R [the metricType R of T] [the metricType R of real_norm_metric_space hNY] mu V (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) a ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall r:R,0<r ->r<d ->
    exists J:R,is_measure_subset_integral mu (metric_closed_ball a r)
      (partial_distance_to (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) (f a)) J%:E /\
      J/(C*r^+n)<eta.
Proof.
move=>hBalls hLebesgue.
have hPositive r:0<r ->0<C*r^+n.
  move=>hr; apply:mulr_gt0; first exact:(@euclidean_closed_unit_volume_laws R n).2.
  exact:exprn_gt0.
exact:(@lebesgue_point_ball_mean_small R [the metricType R of T] (real_norm_metric_space hNY)
  mu V (fun z=>(f z:real_norm_metric_space hNY)) a (fun r=>C*r^+n)
  hBalls (fun r hr=>@euclidean_norm_closed_ball_measure R n a r hr)
  hPositive (fun r hr=>@euclidean_locally_integrable_ball_distance a r hr) hLebesgue).
Qed.
End EuclideanLocalDistanceMeans.
