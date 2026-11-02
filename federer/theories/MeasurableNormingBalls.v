(** Federer (1969), 2.9.22, p. 167: measurable scalar evaluations determine
    norm measurability in a separable space. This supporting step identifies
    closed-ball inverse images with countable intersections of scalar
    inverse images. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureCountableClosure MeasurableFunctionUP MeasurableFunctionBorel
  TopologicalBorel MetricClosedBalls DenseNormingFunctionals DenseNormingNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_norming_closed_ball_preimage]: direct
    supporting countable norm test for the measurability observation
    of Federer 2.9.22, p. 167. All scalar functions are
    genuine total real maps. Closed balls, including negative
    radius empty balls and the zero-radius singleton, require
    no almost-everywhere replacement in this identity. *)
Theorem measurable_norming_closed_ball_preimage (R : realType) (X : choiceType)
    (E D : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R) (k : E -> D)
    (hk : is_dual_norming_family N ed DN k)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (u : X -> E) :
  countable C -> dense C ->
  (forall c, C c -> is_measure_measurable_function mu
    (partial_function_total (fun x => (ed (k c) (u x) : real_line_metric R)))) ->
  forall y r, measure_measurable mu [set x | N (u x-y)<=r].
Proof.
move=> hCc hCd hu y r.
pose A c : set X := [set x | `|ed (k c) (u x)-ed (k c) y|<=r].
have hA c : C c -> measure_measurable mu (A c).
  move=> hc.
  have hb := @measurable_function_borel_preimage R X (real_line_metric R) mu hm
    (partial_function_total (fun x => (ed (k c) (u x) : real_line_metric R)))
    (hu c hc) (metric_closed_ball (ed (k c) y : real_line_metric R) r)
    (closed_borel_set (@metric_closed_ball_closed R
      [the metricType R of real_line_metric R] _ r)).
  rewrite partial_function_total_preimage in hb.
  have he : (fun x => (ed (k c) (u x) : real_line_metric R)) @^-1`
      metric_closed_ball (ed (k c) y : real_line_metric R) r = A c.
    apply/seteqP; split=> x; rewrite /A /metric_closed_ball /=
      real_line_metric_distanceE distrC; by [].
  by rewrite he in hb.
have he : [set x | N (u x-y)<=r] = \bigcap_(c in C) A c.
  apply/seteqP; split=> x hx.
  - move=> c hc; have hh := (dense_norming_family_norm_bound hk hCd (u x-y) r).1 hx c hc.
    by move: hh; rewrite (linearB (hom_as_linear (ed (k c))) (u x) y) !hom_as_linearE.
  - apply: (dense_norming_family_norm_bound hk hCd (u x-y) r).2=> c hc.
    rewrite (linearB (hom_as_linear (ed (k c))) (u x) y) !hom_as_linearE.
    exact: hx c hc.
rewrite he.
exact (@measure_measurable_countable_intersection R X
  [the choiceType of real_norm_metric_space hN] mu hm C A hCc hA).
Qed.
