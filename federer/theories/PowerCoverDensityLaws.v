(** Federer (1969), 2.10.29, pp. 194–195: pass between real power-gauge
    local bounds and the finite-diameter density predicate used for
    Cartesian powers. A positive competing measure with vanishing density
    forces infinite target power measure by the covering infimum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower MetricDiameterUP MetricDiameter MetricRealPowerCost MetricRealPowerMeasure
  MeasureUP CaratheodoryVanishingDensity PowerCoverDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gauge_bounds_give_vanishing_power_density]: supporting
    finite-bound form of the local estimate
    in 2.10.29, pp. 194–195. The
    real exponent is nonnegative, including zero. *)
Lemma gauge_bounds_give_vanishing_power_density (R : realType) (X : metricType R)
    (p : R) (nu : set X -> \bar R) :
  (0<=p)%R ->
  (forall e : R, (0<e)%R -> exists delta : R, (0<delta)%R /\
    forall S, extended_metric_diameter S<=delta%:E -> nu S<=e%:E*metric_real_diameter_cost 1%R p S) ->
  is_vanishing_power_cover_density p nu.
Proof.
move=> hp hlocal e he; have [delta [hd hbound]] := hlocal e he.
exists delta; split=> // S d hd0 hdd hdiam.
have hcomp := @metric_real_power_cost_monotone R 1%R p _ d%:E ler01 hp
  (metric_diameter_nonnegative (extended_metric_diameter_specification S)) hdiam.
have hcut : extended_metric_diameter S<=delta%:E.
  apply: le_trans hdiam _; by rewrite lee_fin.
apply: le_trans (hbound S hcut) _.
have he0 : 0<=e%:E by rewrite lee_fin; exact: ltW he.
have hh := lee_wpmul2l he0 hcomp.
by rewrite metric_real_power_cost_finite mul1r -EFinM in hh.
Qed.

(** Source for [vanishing_power_density_infinite_measure]: supporting
    final covering argument for the higher
    products in 2.10.29, p. 195. The
    target coefficient b is any positive real,
    and the positive competing mass may be infinite. *)
Theorem vanishing_power_density_infinite_measure (R : realType) (X : metricType R)
    (p b : R) (nu : set X -> \bar R) (A : set X) :
  (0<b)%R -> is_measure nu -> 0<nu A -> is_vanishing_power_cover_density p nu ->
  @metric_real_power_measure R X b p A=+oo.
Proof.
move=> hb hn hpos hdensity.
apply: (@caratheodory_vanishing_generator_density R X _ _ _ _ nu A
  (@metric_real_power_measure_specification R X b p) hn hpos)=> e he.
have heps : (0<e*b)%R := mulr_gt0 he hb.
have [delta [hd hbound]] := hdensity (e*b)%R heps.
exists delta; split=> // S hdiam.
pose D := extended_metric_diameter (val S).
have hD0 : 0<=D := metric_diameter_nonnegative (extended_metric_diameter_specification (val S)).
have hDfin : D< +oo := le_lt_trans hdiam (ltry delta).
have hDnum : D \is a fin_num by rewrite (ge0_fin_numE hD0).
pose d := fine D.
have hDeq : D=d%:E := esym (fineK hDnum).
have hd0 : (0<=d)%R by move: hD0; rewrite hDeq lee_fin.
have hdc : (d<=delta)%R by move: hdiam; rewrite -/D hDeq lee_fin.
have hsize : extended_metric_diameter (val S)<=d%:E by rewrite -/D hDeq.
have hh := hbound (val S) d hd0 hdc hsize.
by rewrite /metric_real_diameter_cost -/D hDeq metric_real_power_cost_finite -EFinM mulrA.
Qed.
