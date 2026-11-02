(** Federer (1969), 2.10.21, p. 183: the closed profile image Omega(F_(a,r))
    is compact as a subset of the anchored Lipschitz family. Use the proved
    closedness and the preceding compact-ball product argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic
  CompactSetDistanceProfile CompactBallProfiles CompactBallProfilesClosed
  LipschitzFunctionCompact RealLineBoundedCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_ball_profiles_compact]: direct
    compactness of Omega(F_(a,r)) in 2.10.21,
    p. 183. The supporting result also allows radius zero. *)
Theorem compact_ball_profiles_compact (R : realType) (X : metricType R) (a : X) (r : R) :
  metric_boundedly_compact X -> 0<=r -> compact (compact_ball_profiles a r).
Proof.
move=> hX hr.
have hc := @compact_ball_profiles_closed R X a r hX hr.
have hbig := @anchored_lipschitz_functions_compact R X [the metricType R of real_line_metric R]
  1 a 0 r (@real_line_boundedly_compact R) (@ler01 R) hr.
apply: (subclosed_compact hc hbig)=> f [C [hC ->]].
split; first exact: compact_set_distance_profile_lipschitz.
have [c hcmem] := (set_valP C).2.
have hh := @metric_set_distance_lower R X (val C) (compact_set_distance_profile C)
  (compact_set_distance_profile_specification C) a c hcmem.
have hbound := le_trans hh (hC c hcmem).
change (is_true (`|compact_set_distance_profile C a-0|<=r)).
rewrite subr0.
rewrite (ger0_norm (metric_set_distance_nonnegative (compact_set_distance_profile_specification C) a)).
exact hbound.
Qed.
