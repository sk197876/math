(** Federer (1969), 4.1.5, p. 350:
    the original positive-radius ball quotient.
    Each sufficiently small radius has a finite
    numerator integral and a strictly positive
    finite denominator. No value is assigned
    to an undefined quotient. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureSubsetIntegral MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_ball_integral_quotient_limit]: the literal
    limit of the scalar ball integrals divided
    by their measure, Federer 4.1.5, p. 350.
    All domain qualifications are explicit. *)
Definition is_ball_integral_quotient_limit (R:realType) (X:metricType R)
    (mu:set X->\bar R) (f:partial_function X (extended_real_line R)) (x:X) (l:R):Prop:=
  forall eta:R,0<eta ->exists d:R,0<d /\forall r:R,0<r ->r<d ->
    exists J mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass /\
      is_measure_subset_integral mu (metric_closed_ball x r) f J%:E /\`|J/mass-l|<eta.
