(** Federer (1969), 3.4.8(13), p. 336:
    a uniform ball bound gives the printed diameter
    growth bound for all bounded subsets. Zero diameter
    is handled by the existing zero-cost nullity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter CoveringFamilyUP
  HausdorffMeasure HausdorffDiameterCost HausdorffFibreCost MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_ball_diameter_growth]: the final
    diameter inequality in 3.4.8(13), p. 336.
    This connection applies to all subsets of S;
    measurability of the tested subset is not needed. *)
Theorem hausdorff_ball_diameter_growth (R:realType) (X:metricType R) m
    (S:set X) (c:R):
  (0<m)%N ->0<=c ->
  (forall x r,0<r ->(@hausdorff_measure R X m (S `&` metric_closed_ball x r)<=(c*r^+m)%:E)%E) ->
  forall T:set X,T `<=` S ->metric_set_bounded T ->
    (@hausdorff_measure R X m T<=c%:E*(extended_metric_diameter T)^+m)%E.
Proof.
move=>hPositive hC hBall T hTS hBound.
pose d:=extended_metric_diameter T.
have hDNonnegative:(0<=d)%E:=metric_diameter_nonnegative (extended_metric_diameter_specification T).
have hFinite:d \is a fin_num by rewrite (ge0_fin_numE hDNonnegative);exact:hBound.
have hD:d=(fine d)%:E:=esym (fineK hFinite).
have hRealNonnegative:0<=fine d by move:hDNonnegative;rewrite hD lee_fin.
case:(pselect (T !=set0))=>[[a ha]|hEmpty].
- case:(eqVneq (fine d) 0)=>hZero.
  + have hDiameter:extended_metric_diameter T=0%E by rewrite -/d hD hZero.
    have hCost:hausdorff_diameter_cost m T=0%E.
      rewrite /hausdorff_diameter_cost /hausdorff_power_cost hDiameter.
      clear hBall;case:m hPositive=>[|p] // _;by rewrite expeS mul0e mule0.
    rewrite (hausdorff_zero_cost_generator_null hCost).
    apply:mule_ge0;first by rewrite lee_fin.
    exact:expe_ge0 hDNonnegative.
  + have hRadius:0<fine d by rewrite lt_def hZero hRealNonnegative.
    have hInBall:T `<=` S `&` metric_closed_ball a (fine d).
      move=>x hx;split;first exact:hTS x hx.
      have hDistance:=metric_diameter_upper (extended_metric_diameter_specification T) ha hx.
      by rewrite -/d hD lee_fin in hDistance.
    have hMass:=le_trans (measure_mono (@hausdorff_measure_is_measure R X m) hInBall) (hBall a _ hRadius).
    rewrite -/d hD -EFin_expe -EFinM.
    exact:hMass.
- have hT:T=set0 by apply/seteqP;split=>[x hx|x []];exfalso;apply:hEmpty;by exists x.
  rewrite hT (measure_empty (@hausdorff_measure_is_measure R X m)).
  apply:mule_ge0;first by rewrite lee_fin.
  exact:expe_ge0 (metric_diameter_nonnegative (extended_metric_diameter_specification set0)).
Qed.
