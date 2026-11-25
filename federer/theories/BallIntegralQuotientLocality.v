(** Federer (1969), 4.1.5, p. 350:
    the small-ball quotient depends only on
    the measure and integrals in a neighbourhood
    of its centre. The same original numerator
    and positive finite denominator are preserved
    by compact localization and open inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureSubsetIntegral
  MetricClosedBalls BallIntegralQuotientLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ball_integral_quotient_locality]: the local
    transfer of the exact positive-radius ball
    formula in Federer 4.1.5, p. 350.
    The hypotheses are identities of actual
    integrals and measures, not assumed limits. *)
Theorem ball_integral_quotient_locality (R:realType) (X Y:metricType R)
    (mu:set X->\bar R) (nu:set Y->\bar R) (i:X->Y)
    (f:partial_function X (extended_real_line R)) (g:partial_function Y (extended_real_line R))
    (x:X) (l cap:R):
  0<cap ->
  (forall r,0<r ->r<cap ->nu (metric_closed_ball (i x) r)=mu (metric_closed_ball x r)) ->
  (forall r,0<r ->r<cap ->forall J:R,
    is_measure_subset_integral nu (metric_closed_ball (i x) r) g J%:E ->
    is_measure_subset_integral mu (metric_closed_ball x r) f J%:E) ->
  is_ball_integral_quotient_limit nu g (i x) l ->
  is_ball_integral_quotient_limit mu f x l.
Proof.
move=>hCap hMass hIntegral hLimit eta hEta.
have[d [hD hClose]]:=hLimit eta hEta.
exists (Num.min cap d); split; first by rewrite lt_min hCap hD.
move=>r hR hSmall.
have /andP [hRCap hRD]:(r<cap)&&(r<d) by move:hSmall; rewrite lt_min.
have[J [mass [hMassValue [hPositive [hJ hError]]]]]:=hClose r hR hRD.
exists J,mass; split; first by rewrite -(hMass r hR hRCap).
split=>//; split=>//; exact:hIntegral r hR hRCap J hJ.
Qed.
