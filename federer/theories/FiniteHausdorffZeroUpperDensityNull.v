(** Federer (1969), 3.3.18, p. 301: a finite Hausdorff-mass
    carrier contains no positive mass at zero upper density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic RegularMeasureUP MetricDensities
  HausdorffMeasure HausdorffUpperMetricDensity ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_hausdorff_zero_upper_density_null]: the first
    displayed nullity assertion in the proof of Federer 3.3.18,
    p. 301. Actual 2.10.19(1) with every positive threshold and
    a finite-error squeeze gives nullity on any original finite
    Hausdorff-mass set of zero upper density. No measurability of
    the source or finiteness of its original measure is assumed. *)
Theorem finite_hausdorff_zero_upper_density_null (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (A:set X):
  is_measure psi ->is_regular_measure psi ->
  @hausdorff_measure R X m A< +oo ->
  (forall a,A a ->upper_metric_density m psi a= 0) ->psi A= 0.
Proof.
move=>hPsi hRegular hFinite hZero.
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hNum:H A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hH A)).
have hValue:H A=(fine (H A))%:E:=esym (fineK hNum).
have hFine:(0<=fine (H A))%R:=fine_ge0 (measure_nonnegative hH A).
have hCoefficient:(0<=2^+m*fine (H A))%R by apply:mulr_ge0; rewrite ?exprn_ge0 // ler0n.
have hUpper:psi A<= 0.
  apply:(@extended_upper_bound_from_scaled_errors R (psi A) 0 (2^+m*fine (H A))%R hCoefficient)=>e he.
  have hPoint a:A a ->upper_metric_density m psi a<e%:E.
    by move=>ha; rewrite (hZero a ha) lte_fin.
  have hBound:=@hausdorff_upper_metric_density_bound R X m psi A e hPsi hRegular he hPoint.
  rewrite -/H hValue -EFinM in hBound.
  have hProduct:(2^+m*e*fine (H A)=0+2^+m*fine (H A)*e)%R by nra.
  by rewrite hProduct in hBound.
apply/eqP; by rewrite eq_le hUpper (measure_nonnegative hPsi A).
Qed.
