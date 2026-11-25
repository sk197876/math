(** Boundary regressions for Federer's real-degree density estimates,
    2.10.19, p. 181. These examples check actual density values at zero
    degree and at a nonintegral degree, rather than discretizing degrees. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricDensities RealMetricDensityLimits
  RealHausdorffUpperMetricDensity RealHausdorffSubcriticalMetricDensity
  RealSphericalMetricDensityTheorems PositiveRadiusLimitCongruence
  MetricClosedBalls PointMassMeasure PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_zero_degree_point_density]: project regression
    for the degree-zero endpoint in Federer 2.10.19, p. 181. The unit
    point mass has density one at its own centre in every metric space,
    including spaces with isolated points and diameter-zero balls. *)
Theorem real_zero_degree_point_density (R : realType) (X : metricType R)
    (a : X) :
    partial_function_graph
      (real_metric_density (lexx (0%R : R)) (point_mass R a)) a 1.
Proof.
have hq r (hr : (0<r)%R) :
    real_metric_ball_density (lexx (0%R : R)) (point_mass R a) a r = 1.
  rewrite real_metric_ball_density_zero_degree.
  apply: point_mass_in; rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
have [hu hl] := positive_radius_limits_congr hq.
have [hcu hcl] := @positive_radius_limits_constant R 1.
apply/real_metric_density_graph; split.
- exact: eq_trans hu hcu.
- exact: eq_trans hl hcl.
Qed.

(** Source for [real_half_degree_zero_density]: project regression
    for the nonintegral degrees in Federer 2.10.19, p. 181. With the
    actual Gamma-normalized half-degree denominator, the zero measure
    has both densities zero at every point. *)
Theorem real_half_degree_zero_density (R : realType) (X : metricType R)
    (hp : (0<=(1/2 : R))%R) (a : X) :
    partial_function_graph
      (real_metric_density hp (fun _ : set X => (0 : \bar R))) a 0.
Proof.
have hq r (hr : (0<r)%R) :
    real_metric_ball_density hp (fun _ : set X => (0 : \bar R)) a r = 0.
  by rewrite /real_metric_ball_density mul0e.
have [hu hl] := positive_radius_limits_congr hq.
have [hcu hcl] := @positive_radius_limits_constant R 0.
apply/real_metric_density_graph; split.
- exact: eq_trans hu hcu.
- exact: eq_trans hl hcl.
Qed.
