(** Federer (1969), 3.2.40, p. 276: finite actual
    power-gauge mass below degree one implies zero actual
    Hausdorff length, using the covering laws of 2.10.1--2,
    pp. 170--171. No fractional Gamma normalization is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealPower RealPowerContinuity SubunitPowerDiameterBound
  MetricRealPowerCost MetricRealPowerMeasure MetricDiameter MetricDiameterUP
  HausdorffLengthUP HausdorffLength CaratheodoryLimitUP
  MetricScaleEnvelope MetricScaleEnvelopeUP MetricScaleEnvelopeLaws CaratheodoryBorelRegular MetricScaleCutoffCost MetricScaleWeightedBound
  MeasureUP MeasureBasic ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_subunit_power_mass_zero_length]: the
    dimension-drop argument invoked by Federer 3.2.40, p. 276,
    for the actual power gauge of 2.10.2(1), p. 171.
    Any finite unit-coefficient p-power mass, 0<p<1, forces
    actual Hausdorff length zero, for arbitrary metric spaces
    and arbitrary source sets. Compare costs at smaller cutoffs
    and remove one finite error, with no measurability premise. *)
Theorem finite_subunit_power_mass_zero_length (R:realType) (X:metricType R)
    (p:R) (A:set X):
  (0<p)%R ->(p<1)%R ->@metric_real_power_measure R X 1 p A < +oo ->
  @hausdorff_length R X A=0.
Proof.
move=>hp hp1 hFinite.
pose mu:=@metric_real_power_measure R X 1 p.
have hMu:=@metric_real_power_measure_specification R X 1 p.
have hNonnegative:=measure_nonnegative (@metric_real_power_measure_is_measure R X 1 p ler01) A.
change (is_true (mu A < +oo)%E) in hFinite.
change (is_true (0<=mu A)%E) in hNonnegative.
case hValue:(mu A) hNonnegative hFinite=>[a| |] hNonnegative hFinite; last 2 first.
- by rewrite ltxx in hFinite.
- by [].
have ha:(0<=a)%R by move:hNonnegative; rewrite lee_fin.
have hGap:(0<1-p)%R by lra.
have hLength:=@hausdorff_length_specification R X.
apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_length_is_measure R X)) andbT.
apply:(caratheodory_limit_least hLength)=>tau xi hTau hXi.
apply:(@extended_upper_bound_from_scaled_errors R (xi A) 0 1 ler01)=>e he.
rewrite add0r mul1r.
have ha1:(0<a+1)%R by lra.
have hBudget:(0<e/(a+1))%R by rewrite divr_gt0.
pose root:=real_power (e/(a+1))%R ((1-p)^-1)%R.
have hRoot:(0<root)%R:=@real_power_strictly_positive R (e/(a+1))%R ((1-p)^-1)%R hBudget.
have hRootPower:real_power root (1-p)=(e/(a+1))%R.
  exact:(@real_power_inverse_power R (e/(a+1))%R (1-p)%R (ltW hBudget) hGap).
have [j hCutoff]:=reciprocal_metric_cutoffs_cofinal hTau.
pose b:=((j.+1%:R:R)^-1)%R.
have hb:(0<b)%R by rewrite /b invr_gt0 ltr0n.
pose delta:=Num.min b root.
have hDelta:(0<delta)%R by rewrite /delta lt_min hb hRoot.
have hDeltaB:(delta<=b)%R by rewrite /delta ge_min lexx.
have hDeltaRoot:(delta<=root)%R by rewrite /delta ge_min lexx orbT.
have hDeltaTau:delta%:E<=tau:=le_trans (lee_tofin hDeltaB) hCutoff.
pose factor:=real_power delta (1-p)%R.
have hFactor:(0<factor)%R:=@real_power_strictly_positive R delta (1-p)%R hDelta.
have hFactorBound:(factor<=e/(a+1))%R.
  rewrite -hRootPower; exact:(@real_power_monotone R delta root (1-p)%R (ltW hDelta) hDeltaRoot hGap).
pose phi:=@metric_scale_envelope R X (@nonempty_metric_sets R X) (fun S=>val S)
  (fun S=>metric_real_diameter_cost 1 p (val S)) delta%:E.
have hPhi:=@metric_scale_envelope_specification R X (@nonempty_metric_sets R X) (fun S=>val S)
  (fun S=>metric_real_diameter_cost 1 p (val S)) delta%:E.
have hXiMeasure:is_measure xi.
  exact:metric_scale_envelope_is_measure hXi (fun S=>metric_diameter_nonnegative (extended_metric_diameter_specification (val S))).
have hGenerator (S:@nonempty_metric_sets R X):extended_metric_diameter (val S)<=delta%:E ->
    xi (val S)<=factor%:E*metric_real_diameter_cost 1 p (val S).
  move=>hSmall.
  have hBound:=@metric_scale_generator_bound R X (@nonempty_metric_sets R X)
    (fun T=>val T) (fun T=>extended_metric_diameter (val T)) tau xi S hXi
    (metric_diameter_nonnegative (extended_metric_diameter_specification (val S)))
    (le_trans hSmall hDeltaTau).
  apply:le_trans hBound _.
  have hD0:=metric_diameter_nonnegative (extended_metric_diameter_specification (val S)).
  case hD:(extended_metric_diameter (val S)) hD0 hSmall=>[d| |] hD0 hSmall; last 2 first.
  - by rewrite leye_eq in hSmall.
  - by [].
  have hd:(0<=d)%R by move:hD0; rewrite lee_fin.
  have hdDelta:(d<=delta)%R by move:hSmall; rewrite lee_fin.
  rewrite /metric_real_diameter_cost hD metric_real_power_cost_finite !mul1r -EFinM lee_fin.
  exact:(@subunit_power_diameter_bound R p d delta hp hp1 hd hdDelta hDelta).
have hBound:=@measure_bounded_by_scaled_metric_envelope R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost 1 p (val S)) delta%:E phi xi factor
  hPhi hXiMeasure hFactor hGenerator A.
have hUpper:=@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost 1 p (val S)) mu hMu A delta%:E phi
  (ltac:(by rewrite lte_fin)) hPhi.
have hFactorNonnegative:0<=factor%:E by rewrite lee_fin; exact:ltW hFactor.
have hScaled:=le_trans hBound (lee_wpmul2l hFactorNonnegative hUpper).
rewrite hValue -EFinM in hScaled.
have hApprox:((e/(a+1))*a<=e)%R.
  have haPlus:(a<=a+1)%R by lra.
  have h:=ler_wpM2l (ltW hBudget) haPlus.
  by rewrite divfK ?gt_eqF in h.
apply:le_trans hScaled _; rewrite lee_fin.
exact:le_trans (ler_wpM2r ha hFactorBound) hApprox.
Qed.
