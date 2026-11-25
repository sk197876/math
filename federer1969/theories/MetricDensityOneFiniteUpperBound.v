(** Federer (1969), 3.3.17, pp. 300–301: transfer an
    actual finite upper-density bound at a relative density-one point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureDerivationContext MeasureDerivates
  CenteredBallRelations CenteredRatioOneLocalMass EuclideanBallVolume MetricDensities
  PositiveRadiusLimits PositiveRadiusLimitBounds ExtendedRealBounds ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_density_one_finite_upper_bound]: supporting
    the density-one contradiction in Federer 3.3.17, pp. 300–301.
    If the ORIGINAL relative derivate is one and the original
    numerator has upper m density at most finite b>= 0, then the
    original denominator has the SAME upper bound. All original
    radii remain. Finiteness of the denominator density is derived,
    so this helper does not exclude infinite densities in the
    final numbered criterion. *)
Theorem metric_density_one_finite_upper_bound (R:realType) (X:metricType R) m
    (psi nu:set X->\bar R) (a:X) (b:R):
  is_derivation_measure psi ->
  partial_function_graph (measure_derivate nu psi (@centered_closed_ball_relation R X)) a 1 ->
  (0<=b)%R ->upper_metric_density m nu a<=b%:E ->upper_metric_density m psi a<=b%:E.
Proof.
move=>hPsi hOne hB hUpper.
have hK:(0<=b+2)%R by lra.
apply:(@extended_upper_bound_from_scaled_errors R _ b (b+2)%R hK)=>error hError.
pose t:=Num.min error 1%R.
have hT:(0<t)%R by rewrite /t lt_min hError ltr01.
have hT1:(t<= 1)%R by rewrite /t ge_min lexx orbT.
have hTE:(t<=error)%R by rewrite /t ge_min lexx.
have hLam:(1<1+t)%R by rewrite ltrDl.
have [dPsi [hDPsi hMass]]:=@centered_density_one_local_mass_comparison R X psi nu a
  (1+t)%R hPsi hOne hLam.
have hStrict:upper_metric_density m nu a<(b+t)%R%:E.
  apply:le_lt_trans hUpper _; by rewrite lte_fin ltrDl.
have [dNu [hDNu hNuSup]]:=(positive_radius_upper_lt_iff (metric_ball_density m nu a) _).1 hStrict.
pose d:=Num.min dPsi dNu.
have hD:(0<d)%R by rewrite /d lt_min hDPsi hDNu.
apply:(@positive_radius_upper_eventual_bound R (metric_ball_density m psi a) _ d hD)=>r /andP[hr hrD].
have hMinPsi:(d<=dPsi)%R by rewrite /d ge_min lexx.
have hMinNu:(d<=dNu)%R by rewrite /d ge_min lexx orbT.
have hRPsi:(r<dPsi)%R:=lt_le_trans hrD hMinPsi.
have hRNu:(r<dNu)%R:=lt_le_trans hrD hMinNu.
have hRadiusPsi:(0<r<dPsi)%R by apply/andP; split.
have hMassR:=hMass r hRadiusPsi.
have hValue:positive_radius_values (metric_ball_density m nu a) dNu (metric_ball_density m nu a r).
  exists r; split; last by [].
  by apply/andP; split.
have hNuBound:=ltW (le_lt_trans (extended_real_sup_upper hValue) hNuSup).
have hDen:=metric_ball_density_denominator_positive m hr.
have hInverse:(0<=((euclidean_unit_ball_volume R m*r^+m)%:E)^-1)%E.
  rewrite inve_ge0 lee_fin; exact:ltW hDen.
have hNormal:=lee_wpmul2r hInverse hMassR.
rewrite -muleA in hNormal.
change (is_true (metric_ball_density m psi a r<=(1+t)%R%:E*metric_ball_density m nu a r)%E) in hNormal.
apply:le_trans hNormal _.
have hFactor:(0<=(1+t)%R%:E)%E by rewrite lee_fin; lra.
apply:le_trans (lee_wpmul2l hFactor hNuBound) _.
rewrite -EFinM lee_fin.
have hSquare:(t*t<=t)%R.
  have h:=ler_wpM2l (ltW hT) hT1; by rewrite mulr1 in h.
have hErrorBound:=ler_wpM2l hK hTE.
nra.
Qed.
