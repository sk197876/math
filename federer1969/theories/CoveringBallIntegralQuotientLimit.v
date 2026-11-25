(** Federer (1969), 4.1.5, p. 350:
    the 2.9.8 covering-relation limit gives
    the printed positive-radius ball quotient.
    The diameter bound is enough in every
    dimension; no positive-radius ball is assumed
    to have diameter exactly twice its radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureSubsetIntegral MeasureIntegralUP
  MetricClosedBalls MetricDiameterUP MetricDiameter CenteredBallRelations CoveringRelationLimits
  CoveringFiniteLimitBounds MeasureMeanFunction FiniteMeanPartValues BallIntegralQuotientLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [covering_ball_integral_quotient_limit]: the
    exact conversion to the printed ball quotient
    in Federer 4.1.5, p. 350, from
    2.9.8. All original denominators are retained. *)
Theorem covering_ball_integral_quotient_limit (R:realType) (X:metricType R)
    (mu:set X->\bar R) (f:partial_function X (ExtendedRealOrderTopology.extended_real_line R)) (x:X) (l:R):
  (forall r:R,0<r ->exists mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass) ->
  (forall r:R,0<r ->exists J:R,is_measure_subset_integral mu (metric_closed_ball x r) f J%:E) ->
  partial_function_graph (covering_relation_limit (@centered_closed_ball_relation R X)
    (measure_mean_function mu f)) x l%:E ->
  is_ball_integral_quotient_limit mu f x l.
Proof.
move=>hMass hIntegral hLimit eta hEta.
have[d [hD hSmall]]:=@covering_finite_limit_small_values R X
  (@centered_closed_ball_relation R X) (measure_mean_function mu f) x l eta hLimit hEta.
exists (d/3); split; first by rewrite divr_gt0 // ltr0n.
move=>r hR hRD.
have[mass [hMassValue hMassPositive]]:=hMass r hR.
have[J hJ]:=hIntegral r hR.
have hMean:=finite_measure_mean_value hJ hMassValue hMassPositive.
have hDiameter:(extended_metric_diameter (metric_closed_ball x r)<d%:E)%E.
  have hBound:(extended_metric_diameter (metric_closed_ball x r)<=(r+r)%:E)%E.
    apply:(metric_diameter_least (extended_metric_diameter_specification _)).
    - rewrite lee_fin; exact:addr_ge0 (ltW hR) (ltW hR).
    - move=>z w hz hw; rewrite lee_fin; exact:metric_closed_ball_diameter_bound hz hw.
  apply:le_lt_trans hBound _; rewrite lte_fin; lra.
have hRelated:centered_closed_ball_relation x (metric_closed_ball x r) by exists r.
have[hLo hHi]:=hSmall _ _ hRelated hDiameter hMean.
exists J,mass; split=>//; split=>//; split=>//.
rewrite ltr_norml; apply/andP; move:hLo hHi; rewrite !lte_fin; lra.
Qed.
