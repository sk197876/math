(** Federer (1969), 3.3.17, p. 300: each original
    strict conical density criterion supplies actual uniform tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanBallVolume
  StructureCone StructureConeBasic StructureConeMetric StructureProjectionKernel
  StructureSmallConeCriterionUP StructureConeBoundTests StructureConeCostBounds
  MetricDensities MetricDensityNumericalBounds MetricClosedBalls PositiveRadiusLimits PositiveRadiusLimitBounds
  ExtendedRealBounds ExtendedRealOrderTopology MeasureUP MeasureBasic MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_small_cone_actual_local_test]: the
    first union assertion in the proof of Federer 3.3.17,
    p. 300. The ORIGINAL strict cone density inequality gives
    positive finite lambda and delta satisfying EVERY original
    radius bound through delta and lambda<c*Theta*. Closed-ball
    conical density bounds the original open truncated cone.
    Infinite original ambient density is retained. *)
Theorem structure_small_cone_actual_local_test (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (p:euclidean_projection_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (s:R):
  is_measure psi ->(0<s<1)%R ->
  upper_metric_density m (measure_restrict psi
    (structure_cone (structure_projection_kernel hmn p) a +oo s)) a<
      (structure_small_cone_constant R m*s^+m)%:E*upper_metric_density m psi a ->
  exists lam delta:R,(0<lam)%R /\(0<delta)%R /\
    structure_density_cone_test hmn psi p s lam delta a.
Proof.
move=>hPsi hS hSmall.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose C:=structure_cone (structure_projection_kernel hmn p) a +oo s.
pose nu:=measure_restrict psi C.
pose c:=structure_small_cone_constant R m.
pose power:=(s^+m)%R.
have hPower:(0<power)%R by rewrite /power exprn_gt0 //; exact:(andP hS).1.
have [q [hBelow hAbove]]:=@extended_rationals_order_dense R _ _ hSmall.
pose T:R:=ratr q.
have hT:(0<T)%R.
  have hNonnegative:=(@metric_densities_nonnegative R [the metricType R of X] m nu a (measure_restrict_is_measure hPsi C)).2.
  have h:=le_lt_trans hNonnegative hBelow; by move:h; rewrite lte_fin.
pose lam:=(T/power)%R.
have hLam:(0<lam)%R by rewrite /lam divr_gt0.
have hCancel:(lam*power=T)%R by rewrite /lam divfK ?gt_eqF.
have hLamBound:lam%:E<c%:E*upper_metric_density m psi a.
  have hScaled:power%:E*lam%:E<power%:E*(c%:E*upper_metric_density m psi a).
    rewrite -[power%:E*lam%:E]EFinM mulrC hCancel muleA -EFinM [(power*c)%R]mulrC.
    exact:hAbove.
  by move:hScaled; rewrite lte_pmul2l ?fin_numE ?lte_fin.
have [d [hd hSup]]:=(positive_radius_upper_lt_iff (metric_ball_density m nu a) T%:E).1 hBelow.
pose delta:=(d/2)%R.
have hDelta:(0<delta)%R by rewrite /delta divr_gt0 // ltr0n.
exists lam,delta; split; first exact:hLam.
split; first exact:hDelta.
split; last exact:hLamBound.
move=>r /andP[hr hrd].
have hrD:(r<d)%R by rewrite /delta in hrd; lra.
have hRadius:(0<r<d)%R by apply/andP; split.
have hValue:positive_radius_values (metric_ball_density m nu a) d (metric_ball_density m nu a r).
  by exists r.
have hCost:=ltW (le_lt_trans (extended_real_sup_upper hValue) hSup).
have hBallBound:=@metric_ball_density_value_bound R [the metricType R of X] m nu a r T hr hCost.
apply:(@structure_cone_cost_mass_bound R n m hmn psi setT p a r s
  (euclidean_unit_ball_volume R m*lam) hr (andP hS).1).2.
rewrite setTI.
have hScalar:(euclidean_unit_ball_volume R m*lam*r^+m*s^+m=
    T*euclidean_unit_ball_volume R m*r^+m)%R.
  rewrite mulrAC -[(euclidean_unit_ball_volume R m*lam*s^+m)%R]mulrA -/power hCancel.
  by rewrite [(euclidean_unit_ball_volume R m*T)%R]mulrC.
rewrite hScalar -mulrA.
apply:le_trans _ hBallBound.
apply:(@measure_mono R _ psi hPsi)=>x hx.
split.
- exact:(@structure_cone_radius_mono R n (n-m) (structure_projection_kernel hmn p)
    a r%:E +oo s (leey r%:E) x hx).
- have hDistance:=((@structure_projection_cone_metricE R n m hmn p a x r%:E s (andP hS).1).1 hx).1.
  change ((mdist a x<=r)%R).
  exact:ltW hDistance.
Qed.
