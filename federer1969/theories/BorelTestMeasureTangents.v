(** Federer (1969), 3.3.18, p. 301: original upper
    densities and tangent cones survive finite Borel regularisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction
  PartialFunctionUP MetricDensities MetricClosedBalls PositiveRadiusLimits
  PositiveRadiusLimitCongruence MeasureApproximateTangentUP MeasureApproximateTangentCriterion
  ApproximateDirectionConeGeometry TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_test_restricted_metric_densities]: the
    Borel-test equality for original restrictions in Federer
    3.3.18, p. 301, with the regularisation defined in 3.3.17.
    Every original Borel test intersected with the actual closed
    radius ball has equal mass. Both original density limits agree,
    including infinite values and degree zero. *)
Theorem borel_test_restricted_metric_densities (R:realType) (X:metricType R) m
    (mu nu:set X->\bar R) (A:set X) (a:X):
  (forall B,borel_set B ->mu B=nu B) ->borel_set A ->
  upper_metric_density m (measure_restrict mu A) a=
    upper_metric_density m (measure_restrict nu A) a /\
  lower_metric_density m (measure_restrict mu A) a=
    lower_metric_density m (measure_restrict nu A) a.
Proof.
move=>hValue hA.
apply:positive_radius_limits_congr=>r hr.
rewrite /metric_ball_density /measure_restrict.
rewrite (hValue _ (borel_family_binary_intersection (borel_sets_family X) hA
  (closed_borel_set (@metric_closed_ball_closed R X a r)))).
by [].
Qed.

(** Source for [borel_test_measure_approximate_tangents]: the
    unchanged original tangent under the finite regularisation in
    Federer 3.3.18, p. 301. Original open directional cones are
    Borel, and the actual 3.2.16 directional criterion identifies
    the tangent from their upper densities. No nullity of the
    added part of a nonmeasurable hull is asserted. *)
Theorem borel_test_measure_approximate_tangents (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) m (mu nu:set X->\bar R) (a:X):
  is_measure mu ->is_measure nu ->
  (forall B:set (real_norm_metric_space hNX),borel_set B ->mu B=nu B) ->
  measure_approximate_tangent_cone hNX mu m a=
    measure_approximate_tangent_cone hNX nu m a.
Proof.
move=>hMu hNu hValue.
pose M:=real_norm_metric_space hNX.
have hDensity v e:=(@borel_test_restricted_metric_densities R M m mu nu
  (approximate_direction_cone NX a v e) a hValue
  (open_borel_set (@approximate_direction_cone_open R X NX hNX a v e))).1.
apply/seteqP; split=>v hV.
- apply:(@measure_approximate_tangent_directional_criterion R X NX hNX nu m a v hNu).2=>e he.
  rewrite -(hDensity v e).
  exact:(@measure_approximate_tangent_directional_criterion R X NX hNX mu m a v hMu).1 hV e he.
- apply:(@measure_approximate_tangent_directional_criterion R X NX hNX mu m a v hMu).2=>e he.
  rewrite (hDensity v e).
  exact:(@measure_approximate_tangent_directional_criterion R X NX hNX nu m a v hNu).1 hV e he.
Qed.
