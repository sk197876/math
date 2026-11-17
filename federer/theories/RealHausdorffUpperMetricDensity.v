(** Federer 2.10.19(1), p. 181, in every nonnegative real degree.
    Apply the existing generic local Caratheodory comparison to the
    original Gamma-normalized diameter costs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricDensityLimits RealMetricDensityHausdorffGauge
  RealHausdorffNormalisation RealHausdorffMeasure RealPower RealPowerCoverVariants
  MetricRealPowerCost HausdorffLengthUP MeasureUP MeasureBasic RegularMeasureUP
  CaratheodoryDensityLocalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_upper_metric_density_bound]: supporting
    positive-threshold form of Federer 2.10.19(1), p. 181. A regular
    measure with upper real-degree density below t on A is bounded by
    2^p*t times the actual Hausdorff measure. A need not be measurable
    or have finite mass. Use the existing regular local-cover theorem. *)
Theorem real_hausdorff_upper_metric_density_bound (R : realType)
    (X : metricType R) (p : R) (hp : (0<=p)%R)
    (mu : set X -> \bar R) (A : set X) (t : R) :
    is_measure mu -> is_regular_measure mu -> (0<t)%R ->
    (forall x, A x -> upper_real_metric_density hp mu x<t%:E) ->
    mu A<=(real_power 2%R p*t)%R%:E*@real_hausdorff_measure R X p hp A.
Proof.
move=> hm hr ht hlim.
have htwo : (0<real_power 2%R p)%R := @real_power_strictly_positive R 2%R p (ltr0n R 2).
have hct : (0<real_power 2%R p*t)%R := mulr_gt0 htwo ht.
have hcost (j : @nonempty_metric_sets R X) :
    0<=metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j).
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hp)).
apply: (@caratheodory_density_local_bound R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j))
  mu (@real_hausdorff_measure R X p hp) A (real_power 2%R p*t)%R hm hr hcost
  (@real_hausdorff_measure_specification R X p hp) hct) => x hx.
have [d [hd hlocal]] := @real_metric_density_local_set_bound R X p hp mu x t hm (hlim x hx).
exists d%:E; split; first by rewrite lte_fin.
move=> j hj hdiam.
have hmono : mu (A `&` val j)<=mu (val j).
  apply: (@measure_mono R X mu hm) => y [_ hy]; exact hy.
exact: le_trans hmono (hlocal (val j) hj hdiam).
Qed.

(** Source for [federer_2_10_19_1_real]: direct original assertion
    of Federer 2.10.19(1), p. 181, in every nonnegative real degree.
    Retain the finite real threshold without imposing positivity:
    the original hypothesis forces it when A is nonempty, and the
    empty case follows from the measure laws. *)
Theorem federer_2_10_19_1_real (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) (A : set X) (t : R) :
    is_measure mu -> is_regular_measure mu ->
    (forall x, A x -> upper_real_metric_density hp mu x<t%:E) ->
    mu A<=(real_power 2%R p*t)%R%:E*@real_hausdorff_measure R X p hp A.
Proof.
move=> hm hr hlim.
case: (pselect (exists x, A x)) => [[x hx]|hn].
- have hn0 := (@real_metric_densities_nonnegative R X p hp mu x hm).2.
  have htE := le_lt_trans hn0 (hlim x hx).
  have ht : (0<t)%R by move: htE; rewrite lte_fin.
  exact: (@real_hausdorff_upper_metric_density_bound R X p hp mu A t hm hr ht hlim).
- have hA : A=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hn; by exists x.
  by rewrite hA (measure_empty hm)
    (measure_empty (@real_hausdorff_measure_is_measure R X p hp)) mule0.
Qed.
