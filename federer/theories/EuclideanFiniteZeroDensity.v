(** Federer (1969), 3.1.4, pp. 214–216: finite unions of
    density-zero exceptional sets support the reduction to scalar
    target coordinates and the union of bad coordinate increments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanNoncenteredVitali EuclideanClosedBallVolume CenteredBallRelations
  PartialFunctionUP MeasureUP MeasureBasic MeasureSetDensity MetricClosedBalls
  CenteredNullSetDensity EuclideanZeroDensityUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_empty_set_density_zero]: empty-family
    boundary of the exceptional-set unions used in Federer 3.1.4,
    pp. 214–216. Every positive-radius ball has positive finite mass,
    including the zero-dimensional source convention. *)
Lemma euclidean_empty_set_density_zero (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) set0) a 0%E.
Proof.
apply: (@centered_null_set_density_zero R _ _ _ a (euclidean_lebesgue_is_measure R n)).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- exact: (measure_empty (euclidean_lebesgue_is_measure R n)).
Qed.

(** Source for [euclidean_finite_union_density_zero]: supporting
    finite-coordinate combination of exceptional sets for Federer
    3.1.4, pp. 214–216. The index type may be empty; no measurability
    of individual sets is required. *)
Theorem euclidean_finite_union_density_zero (R : realType) n (J : finType)
    (A : J -> set (inner_metric_space (@euclidean_inner_productP R n))) a :
  (forall j, partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) (A j)) a 0%E) ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) (\bigcup_j A j)) a 0%E.
Proof.
move=> hA.
have he : (\bigcup_j A j)=\big[setU/set0]_j A j.
  have hh := @bigcup_pred J _ xpredT A.
  have hset : [set j : J | xpredT j]=setT.
    by apply/seteqP; split=> j _.
  by rewrite hset in hh.
rewrite he.
elim/big_rec: _=> [|j B _ hB].
- exact: euclidean_empty_set_density_zero.
- exact: euclidean_zero_density_union (hA j) hB.
Qed.
