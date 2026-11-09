(** Federer (1969), 3.3.17, pp. 300–301: the actual
    density-one derivate controls all sufficiently small ball masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureDerivationContext
  MeasureDerivates CenteredBallRelations CenteredBallRatioDomain NullBallLocus
  CoveringRelationLimits CoveringFiniteLimitBounds MetricClosedBalls MetricDiameterUP MetricDiameter
  CoveringFamilyUP CoveringFamilyLaws ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [centered_density_one_local_mass_comparison]:
    supporting the 2.9.11 density-one step in Federer 3.3.17,
    pp. 300–301. The ORIGINAL partial derivate value one gives
    psi(ball)<=lambda*nu(ball) at EVERY sufficiently small
    positive radius for EVERY lambda>1. Defined quotients,
    positive finite original denominators and ball diameter bounds
    are discharged. The numerator need not be regular or finite. *)
Lemma centered_density_one_local_mass_comparison (R:realType) (X:metricType R)
    (psi nu:set X->\bar R) (a:X) (lam:R):
  is_derivation_measure psi ->
  partial_function_graph (measure_derivate nu psi (@centered_closed_ball_relation R X)) a 1 ->
  (1<lam)%R ->exists delta:R,(0<delta)%R /\forall r:R,(0<r<delta)%R ->
    psi (metric_closed_ball a r)<=lam%:E*nu (metric_closed_ball a r).
Proof.
move=>hPsi hOne hLam.
have hLamPositive:(0<lam)%R:=lt_trans (@ltr01 R) hLam.
have hInverse:(lam^-1<1)%R by rewrite invf_lt1 //; exact:hLam.
pose e:=(1-lam^-1)%R.
have hE:(0<e)%R by rewrite /e subr_gt0.
have [d [hd hSmall]]:=@covering_finite_limit_small_values R X
  (@centered_closed_ball_relation R X) (measure_ratio_function nu psi) a 1%R e hOne hE.
pose delta:=(d/3)%R.
have hDelta:(0<delta)%R by rewrite /delta divr_gt0 // ltr0n.
exists delta; split; first exact:hDelta.
move=>r /andP[hr hrDelta].
have hNotNull:~measure_null_ball_points psi a:=
  @centered_derivate_outside_null_ball_points R X psi nu a 1 (derivation_measure_law hPsi) hOne.
have hDenPositive:=@outside_null_ball_points_positive R X psi a r (derivation_measure_law hPsi) hNotNull hr.
have hDenFinite:psi (metric_closed_ball a r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law hPsi) _)).
  exact:(@derivation_measure_bounded_finite R X psi hPsi _ (@covering_closed_ball_bounded R X a r (ltW hr))).
have hDenValue:psi (metric_closed_ball a r)=(fine (psi (metric_closed_ball a r)))%:E by rewrite fineK.
have hFinePositive:(0<fine (psi (metric_closed_ball a r)))%R by move:hDenPositive; rewrite hDenValue lte_fin.
have hBallDiameter:extended_metric_diameter (metric_closed_ball a r)<d%:E.
  have hRadius:((r+r)<d)%R by rewrite /delta in hrDelta; lra.
  have hStrict:((r+r)%:E<d%:E)%E by rewrite lte_fin.
  apply:le_lt_trans _ hStrict.
  apply:(metric_diameter_least (extended_metric_diameter_specification (metric_closed_ball a r))); first by rewrite lee_fin; exact:addr_ge0 (ltW hr) (ltW hr).
  move=>x y hx hy; rewrite lee_fin; exact:metric_closed_ball_diameter_bound hx hy.
have hRatio:=@centered_ball_ratio_positive_domain R X psi nu a r hPsi hNotNull hr.
have hNear:=hSmall (metric_closed_ball a r) _ (ex_intro _ r (conj hr (erefl _))) hBallDiameter hRatio.
have hLower:=hNear.1.
rewrite /e opprB addrCA subrr addr0 in hLower.
have hScaled:=lee_wpmul2r (ltW hDenPositive) (ltW hLower).
rewrite hDenValue in hScaled.
have hCancel:((fine (psi (metric_closed_ball a r)))^-1)%:E*
    (fine (psi (metric_closed_ball a r)))%:E= 1.
  by rewrite -EFinM mulVf ?gt_eqF.
rewrite inver (gt_eqF hFinePositive) -muleA hCancel mule1 in hScaled.
have hFinal:=lee_wpmul2l (lee_tofin (ltW hLamPositive)) hScaled.
rewrite muleA -EFinM mulfV ?gt_eqF // in hFinal.
rewrite mul1r -hDenValue in hFinal.
exact:hFinal.
Qed.
