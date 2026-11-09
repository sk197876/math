(** Federer (1969), 3.3.4, p. 291: compare
    the actual 2.9.17 ratio with ordinary
    nonnegative-radius expressions only after
    proving every positive denominator is finite
    and positive. No default quotient is used
    at a zero denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureDerivationContext MeasureDerivates
  NullBallLocus CenteredBallRatioDomain RadialBallRatios MetricClosedBalls
  ExtendedRealBounds PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_literal_positive_ball_ratio]:
    the literal positive-radius quotient form
    used in applying 2.9.17 in Federer 3.3.4,
    p. 291. Outside the null-ball locus,
    every positive-radius quotient is actually
    defined, so the partial and literal upper
    limits agree exactly. *)
Theorem structure_literal_positive_ball_ratio (R:realType) (X:metricType R)
    (phi psi:set X->\bar R) (x:X):
  is_derivation_measure phi ->~measure_null_ball_points phi x ->
  centered_ball_ratio_upper_limit psi phi x=
    positive_radius_upper_limit
      (fun r:R=>psi (metric_closed_ball x r)/phi (metric_closed_ball x r)).
Proof.
move=>hPhi hNo.
have hValues d:centered_ball_ratio_values psi phi x d=
    positive_radius_values (fun r:R=>psi (metric_closed_ball x r)/phi (metric_closed_ball x r)) d.
  apply/seteqP; split=>z.
  - move=>[r [hr [hrd hGraph]]].
    have hLiteral:=centered_ball_ratio_positive_domain psi hPhi hNo hr.
    exists r; split; first by apply/andP.
    exact:partial_function_single_valued hGraph hLiteral.
  - move=>[r [/andP [hr hrd] ->]].
    exists r; split=>//; split=>//.
    exact (@centered_ball_ratio_positive_domain R X phi psi x r hPhi hNo hr).
rewrite /centered_ball_ratio_upper_limit /positive_radius_upper_limit.
congr (extended_real_inf _); apply/seteqP; split=>z [d [hd ->]];
  exists d; split=>//; by rewrite hValues.
Qed.
