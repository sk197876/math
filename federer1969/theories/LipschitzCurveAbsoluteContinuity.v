(** Federer (1969), 3.2.46, p. 281: the admissible Lipschitz curves
    have actual derivatives almost everywhere, by the existing curve
    theory of 2.9.22, pp. 167--168. This supporting metric absolute
    continuity assertion is valid for every target metric space. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP
  RealAbsoluteContinuityUP MetricCurveAbsoluteContinuityUP
  MetricCurveAbsoluteContinuityBasic LipschitzRealAbsoluteContinuity
  LocallyAbsolutelyContinuousCurve.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_curve_locally_absolute_continuous]:
    Lipschitz curves satisfy the absolute continuity prerequisite
    of 2.9.22, pp. 167--168, used in Federer 3.2.46, p. 281.
    The supplied Lipschitz bound may be zero. *)
Lemma metric_lipschitz_curve_locally_absolute_continuous (R : realType)
    (Y : metricType R) (C : real_line_metric R -> Y) (L : R) :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y setT C L ->
  is_locally_absolutely_continuous_curve C.
Proof.
move=> [hL hC] a b hab.
have hId : is_absolutely_continuous_real_curve (fun t : R => t) a b.
  apply: (@lipschitz_real_curve_absolutely_continuous R (fun t => t) 1 a b ler01).
  by move=> t u; rewrite mul1r.
have hIdMetric : is_absolutely_continuous_metric_curve
    (fun t : R => (t : real_line_metric R)) a b.
  exact: (metric_absolute_continuity_real_agreement _ _ _).2 hId.
exact: (@metric_absolute_continuity_lipschitz_postcomposition R
  [the metricType R of real_line_metric R] Y C (fun t => t) L a b hL
  (fun x y => hC x y Logic.I Logic.I) hIdMetric).
Qed.
