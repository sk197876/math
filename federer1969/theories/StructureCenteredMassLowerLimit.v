(** Federer (1969), 3.3.7, p. 294: the local ball
    mass bound supplies the actual lower derivate comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureDerivationContext
  MeasureDerivates NullBallLocus CenteredBallRatioDomain CenteredBallRelations
  CoveringRelationLimits CoveringFamilyLaws MetricClosedBalls MetricDiameterUP MetricDiameter
  ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_centered_mass_lower_limit]: supporting the
    differentiation passage in Federer 3.3.7, p. 294, through
    2.9.3–2.9.4 and 2.9.15. Actual positive finite ball denominators
    and arbitrarily small original balls give the lower covering
    limit bound. This includes isolated points; no diameter equality
    or preassigned ordinary derivative is assumed. *)
Theorem structure_centered_mass_lower_limit (R:realType) (X:metricType R)
    (phi psi:set X-> \bar R) (x:X) (C delta:R):
  is_derivation_measure phi ->~measure_null_ball_points phi x ->0<delta ->
  (forall r:R,0<r ->r<delta ->
    (psi (metric_closed_ball x r)<=C%:E*phi (metric_closed_ball x r))%E) ->
  (covering_lower_limit (@centered_closed_ball_relation R X)
    (measure_ratio_function psi phi) x<=C%:E)%E.
Proof.
move=>hPhi hNotNull hDelta hMass.
rewrite /covering_lower_limit; apply:extended_real_sup_least=>v [d [hd ->]].
pose r:=Num.min delta d/3.
have hMin:0<Num.min delta d by rewrite lt_min hDelta hd.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hrDelta:r<delta.
  have hLess:r<Num.min delta d by rewrite /r; lra.
  have hMinDelta:Num.min delta d<=delta by rewrite ge_min lexx.
  exact:lt_le_trans hLess hMinDelta.
have hrD:r<d.
  have hLess:r<Num.min delta d by rewrite /r; lra.
  have hMinD:Num.min delta d<=d by rewrite ge_min lexx orbT.
  exact:lt_le_trans hLess hMinD.
have hDiameter:(extended_metric_diameter (metric_closed_ball x r)<d%:E)%E.
  have hBound:(extended_metric_diameter (metric_closed_ball x r)<=(r+r)%:E)%E.
    apply:(metric_diameter_least (extended_metric_diameter_specification _)).
    - rewrite lee_fin; exact:addr_ge0 (ltW hr) (ltW hr).
    - move=>a b ha hb; rewrite lee_fin; exact:metric_closed_ball_diameter_bound ha hb.
  apply:le_lt_trans hBound _; rewrite lte_fin.
  have hMinD:Num.min delta d<=d by rewrite ge_min lexx orbT.
  rewrite /r; lra.
have hGraph:=@centered_ball_ratio_positive_domain R X phi psi x r hPhi hNotNull hr.
have hRange:covering_value_range (@centered_closed_ball_relation R X)
    (measure_ratio_function psi phi) x d
    (psi (metric_closed_ball x r)/phi (metric_closed_ball x r))%E.
  exists (metric_closed_ball x r); split; first by exists r.
  by split.
apply:le_trans (extended_real_inf_lower hRange) _.
have hm:=derivation_measure_law hPhi.
have hPositive:=outside_null_ball_points_positive hm hNotNull hr.
have hFinite:phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact:(@derivation_measure_bounded_finite R X phi hPhi _
    (covering_closed_ball_bounded x (ltW hr))).
pose t:=fine (phi (metric_closed_ball x r)).
have hT:phi (metric_closed_ball x r)=t%:E by rewrite /t fineK.
have ht:0<t by move:hPositive; rewrite hT lte_fin.
have hInverse:(0<=(t%:E)^-1)%E by rewrite inve_ge0 lee_fin; exact:ltW ht.
have hProduct:=@lee_wpmul2r R (t%:E)^-1 hInverse _ _ (hMass r hr hrDelta).
rewrite hT in hProduct.
rewrite inver (gt_eqF ht) -muleA -EFinM divff ?gt_eqF // mulr1 in hProduct.
rewrite hT inver (gt_eqF ht).
exact:hProduct.
Qed.
