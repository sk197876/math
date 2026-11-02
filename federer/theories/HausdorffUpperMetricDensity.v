(** Federer (1969), 2.10.19(1), p. 181: a strict upper metric-density bound
    t yields mu(A)<=2^m t H^m(A). retain Federer's strict version and
    initial integer degrees here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RegularMeasureUP MetricDensities MetricDensityNumericalBounds
  MetricDensityHausdorffGauge HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  CaratheodoryDensityLocalBound MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_upper_metric_density_bound]: direct
    positive-threshold estimate in 2.10.19(1), p. 181 Use the proved
    small-set estimate and regular exhaustion, without assuming A measurable
    or mu(A) finite. *)
Theorem hausdorff_upper_metric_density_bound (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) (A : set X) (t : R) :
  is_measure mu -> is_regular_measure mu -> (0<t)%R ->
  (forall x, A x -> upper_metric_density m mu x<t%:E) ->
  mu A<=((2 : R)^+m*t)%:E*hausdorff_measure m A.
Proof.
move=> hm hr ht hlim.
have h2 : (0<(2 : R)^+m)%R by rewrite exprn_gt0 // ltr0n.
have hct : (0<(2 : R)^+m*t)%R := mulr_gt0 h2 ht.
have hcost (j : @nonempty_metric_sets R X) : 0<=hausdorff_diameter_cost m (val j).
  exact: hausdorff_diameter_cost_nonnegative.
apply: (@caratheodory_density_local_bound R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) mu (hausdorff_measure m) A
  ((2 : R)^+m*t)%R hm hr hcost (@hausdorff_measure_specification R X m) hct)=> x hx.
have [d [hd hlocal]] := metric_density_local_set_bound hm (hlim x hx).
exists d%:E; split; first by rewrite lte_fin.
move=> j hj hdiam.
have hmono : mu (A `&` val j)<=mu (val j).
  apply: (@measure_mono R X mu hm)=> y [_ hy]; exact hy.
exact: le_trans hmono (hlocal (val j) hj hdiam).
Qed.

(** Source for [federer_2_10_19_1]: direct printed strict
    upper-density implication in 2.10.19(1), p. 181,
    at integer degrees. Positivity of the finite real
    threshold follows from the hypothesis when A is
    nonempty; the empty case needs no added hypothesis. *)
Theorem federer_2_10_19_1 (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) (A : set X) (t : R) :
  is_measure mu -> is_regular_measure mu ->
  (forall x, A x -> upper_metric_density m mu x<t%:E) ->
  mu A<=((2 : R)^+m*t)%:E*hausdorff_measure m A.
Proof.
move=> hm hr hlim.
case: (pselect (exists x, A x))=> [[x hx]|hn].
- have hn0 := (@metric_densities_nonnegative R X m mu x hm).2.
  have htE := le_lt_trans hn0 (hlim x hx).
  have ht : (0<t)%R by move: htE; rewrite lte_fin.
  exact: hausdorff_upper_metric_density_bound hm hr ht hlim.
- have hA : A=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hn; by exists x.
  by rewrite hA (measure_empty hm) (measure_empty (@hausdorff_measure_is_measure R X m)) mule0.
Qed.
