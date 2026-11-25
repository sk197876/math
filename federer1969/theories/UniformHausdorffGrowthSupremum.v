(** Federer (1969), 3.4.8(13), p. 328:
    the common diameter coefficient bounds the literal
    supremum of the displayed mass-to-diameter ratios.
    Zero diameter is retained: its positive-degree mass
    is zero by the proved all-subset growth law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import UniformHausdorffGrowthUP HausdorffMeasure MeasureUP MeasureBasic
  MetricDiameterUP MetricDiameter MetricBoundedClosureLaws CoveringFamilyUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_hausdorff_growth_ratio_supremum]: the literal
    finite supremum in 3.4.8(13), p. 328.
    The original ratios range over every nonempty subset;
    no Borel restriction is added. *)
Theorem uniform_hausdorff_growth_ratio_supremum (R:realType) (X:metricType R) m
    (S:set X) (c:R):
  is_uniform_hausdorff_growth m S c ->
  (extended_real_sup [set q: \bar R|exists T:set X,T !=set0 /\T `<=` S /\
    q=(@hausdorff_measure R X m T/(extended_metric_diameter T)^+m)%E]< +oo)%E.
Proof.
move=>hGrowth.
apply:(le_lt_trans (_:(_<=c%:E)%E) (ltry c)).
apply:extended_real_sup_least=>q [T [hNonempty [hTS ->]]].
have hBound:=@uniform_hausdorff_growth_bound R X m S c hGrowth T hTS.
have hDBound:=metric_bounded_subset hTS (uniform_hausdorff_growth_bounded hGrowth).
have hDNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification T).
have hDFinite:extended_metric_diameter T \is a fin_num by rewrite (ge0_fin_numE hDNonnegative);exact:hDBound.
have hD:extended_metric_diameter T=(fine (extended_metric_diameter T))%:E:=esym (fineK hDFinite).
have hRealNonnegative:0<=fine (extended_metric_diameter T) by move:hDNonnegative;rewrite hD lee_fin.
pose d:=(fine (extended_metric_diameter T))^+m.
have hDReal:0<=d:=exprn_ge0 m hRealNonnegative.
rewrite hD -EFin_expe in hBound *.
case:(eqVneq d 0)=>hZero.
- have hMass:@hausdorff_measure R X m T=0%E.
    apply/eqP;rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R X m) T) andbT.
    by move:hBound;rewrite -/d hZero mule0.
  rewrite hMass mul0e lee_fin;exact:uniform_hausdorff_growth_coefficient hGrowth.
- have hPositive:0<d by rewrite lt_def hZero hDReal.
  by rewrite -/d inver (negbTE hZero) lee_pdivrMr.
Qed.
