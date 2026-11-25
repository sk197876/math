(** Federer (1969), 3.3.9, p. 296: small actual ball
    quotients with unbounded upper growth give infinite upper derivate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureDerivationContext MeasureDerivates CoveringRelationLimits
  CenteredBallRelations CenteredBallRatioDomain NullBallLocus PartialFunctionUP
  MetricClosedBalls MetricDiameterUP MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_centered_upper_infinite]: the passage to
    the infinite-upper-derivate exceptional set of 2.9.5 in Federer
    3.3.9, p. 296. Arbitrarily small positive actual balls with
    arbitrarily large quotient suffice; no ordinary infinite limit
    is assumed. Their actual diameters are bounded by twice the
    radius, and the quotient remains in the original partial domain. *)
Theorem structure_centered_upper_infinite (R:realType) (X:metricType R)
    (phi psi:set X->\bar R) (x:X):
  is_derivation_measure phi ->~measure_null_ball_points phi x ->
  (forall d b:R,0<d ->exists r:R,0<r<d /\
    (b%:E<psi (metric_closed_ball x r)/phi (metric_closed_ball x r))%E) ->
  covering_upper_limit (@centered_closed_ball_relation R X)
    (measure_ratio_function psi phi) x=+oo%E.
Proof.
move=>hPhi hNotNull hWitness.
apply/eqP; rewrite eq_le leey /=.
apply:extended_real_inf_greatest=>v [d [hd ->]].
have hAbove b:(b%:E<extended_real_sup (covering_value_range
    (@centered_closed_ball_relation R X) (measure_ratio_function psi phi) x d))%E.
  have hThird:0<d/3 by rewrite divr_gt0 // ltr0n.
  have [r [/andP [hr hSmall] hLarge]]:=hWitness (d/3) b hThird.
  have hDiameter:(extended_metric_diameter (metric_closed_ball x r)<d%:E)%E.
    have hBound:(extended_metric_diameter (metric_closed_ball x r)<=(r+r)%:E)%E.
      apply:(metric_diameter_least (extended_metric_diameter_specification _)).
      - rewrite lee_fin; exact:addr_ge0 (ltW hr) (ltW hr).
      - move=>y z hy hz; rewrite lee_fin; exact:metric_closed_ball_diameter_bound hy hz.
    apply:le_lt_trans hBound _; rewrite lte_fin; lra.
  have hGraph:=@centered_ball_ratio_positive_domain R X phi psi x r hPhi hNotNull hr.
  apply:lt_le_trans hLarge _; apply:extended_real_sup_upper.
  exists (metric_closed_ball x r); split; first by exists r.
  by split.
case hValue:(extended_real_sup (covering_value_range
    (@centered_closed_ball_relation R X) (measure_ratio_function psi phi) x d))=>[c| |].
- have hBad:=hAbove c; by rewrite hValue ltxx in hBad.
- exact:lexx.
- have hBad:=hAbove 0; by rewrite hValue in hBad.
Qed.
