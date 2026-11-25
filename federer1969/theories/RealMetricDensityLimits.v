(** Federer 2.10.19, p. 181, in every nonnegative real degree. Reuse the
    actual ball quotient and lower density already introduced for 3.3.21;
    add its upper limit and common partial density through the existing
    positive-radius limit laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricDensities RealHausdorffNormalisation
  RealPower MetricClosedBalls MeasureUP MeasureBasic PartialFunctionUP
  PositiveRadiusLimits PositiveRadiusLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [upper_real_metric_density]: direct upper density in
    Federer 2.10.19, p. 181. Its quotient is the existing actual
    Gamma-normalized real-degree ball quotient of 3.3.21. Only strictly
    positive original radii enter the upper limit. *)
Definition upper_real_metric_density (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) (a : X) :=
  positive_radius_upper_limit (real_metric_ball_density hp mu a).

(** Source for [real_metric_density]: direct common density of Federer
    2.10.19, p. 181. Its partial graph consists exactly of agreement
    of the original real-degree upper and lower limits. No value is
    assigned where they disagree. *)
Definition real_metric_density (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) : partial_function X (\bar R).
Proof.
refine (@Build_partial_function X (\bar R)
  (fun x y => upper_real_metric_density hp mu x=y /\
    lower_real_metric_density hp mu x=y) _).
move=> x y z [hy _] [hz _]; exact: eq_trans (esym hy) hz.
Defined.

(** Source for [real_metric_density_graph]: supporting exact graph
    equations for the common density in Federer 2.10.19, p. 181. *)
Lemma real_metric_density_graph (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a y :
    partial_function_graph (real_metric_density hp mu) a y <->
      upper_real_metric_density hp mu a=y /\ lower_real_metric_density hp mu a=y.
Proof. by []. Qed.

(** Source for [real_metric_densities_ordered]: supporting order of
    the original positive-radius limits in Federer 2.10.19, p. 181.
    The general limit theorem needs no measure or finiteness premise. *)
Lemma real_metric_densities_ordered (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a :
    lower_real_metric_density hp mu a<=upper_real_metric_density hp mu a.
Proof. exact: positive_radius_limits_ordered. Qed.

(** Source for [real_metric_densities_nonnegative]: supporting
    nonnegativity for Federer 2.10.19, p. 181. Reuse the already proved
    nonnegative actual real-degree quotient at every positive radius. *)
Lemma real_metric_densities_nonnegative (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a :
    is_measure mu ->
    0<=lower_real_metric_density hp mu a /\ 0<=upper_real_metric_density hp mu a.
Proof.
move=> hm.
have hl : 0<=lower_real_metric_density hp mu a.
  apply: positive_radius_lower_nonnegative => r hr.
  exact: (@real_metric_ball_density_nonnegative R X p hp mu a r hm hr).
split=> //; exact: le_trans hl (real_metric_densities_ordered hp mu a).
Qed.

(** Source for [real_metric_ball_density_zero_degree]: supporting
    degree-zero convention in Federer 2.10.19, p. 181. Gamma
    normalization and the empty power make the quotient equal the
    original ball mass, including radius zero. *)
Lemma real_metric_ball_density_zero_degree (R : realType) (X : metricType R)
    (hp : (0<=0 :> R)%R) (mu : set X -> \bar R) a r :
    real_metric_ball_density hp mu a r=mu (metric_closed_ball a r).
Proof.
by rewrite /real_metric_ball_density real_hausdorff_normalisation_zero
  real_power_zero_exponent mulr1 inve1 mule1.
Qed.

(** Source for [real_metric_ball_density_value_bound]: supporting
    conversion in Federer 2.10.19(1)-(2), p. 181. Multiply by the
    already proved positive finite real-degree denominator. Infinite
    numerator values remain allowed. *)
Lemma real_metric_ball_density_value_bound (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a (r t : R) :
    (0<r)%R -> real_metric_ball_density hp mu a r<=t%:E ->
    mu (metric_closed_ball a r)<=
      (t*(real_hausdorff_normalisation hp*real_power (2*r)%R p))%R%:E.
Proof.
move=> hr hq.
pose d := (real_hausdorff_normalisation hp*real_power (2*r)%R p)%R.
have hdpos : (0<d)%R := @real_metric_density_denominator_positive R p r hp hr.
have hd : 0<=d%:E by rewrite lee_fin; exact: ltW hdpos.
have hh := lee_wpmul2r hd hq.
rewrite /real_metric_ball_density inver (gt_eqF hdpos) -muleA -!EFinM
  mulVf ?gt_eqF // mule1 in hh.
exact hh.
Qed.

(** Source for [real_metric_ball_density_value_large]: supporting
    large-ball comparison in Federer 2.10.19(3), p. 181. The same
    positive finite denominator transfers the strict inequality. *)
Lemma real_metric_ball_density_value_large (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a (r t : R) :
    (0<r)%R -> t%:E<real_metric_ball_density hp mu a r ->
    (t*(real_hausdorff_normalisation hp*real_power (2*r)%R p))%R%:E<
      mu (metric_closed_ball a r).
Proof.
move=> hr hq.
pose d := (real_hausdorff_normalisation hp*real_power (2*r)%R p)%R.
have hdpos : (0<d)%R := @real_metric_density_denominator_positive R p r hp hr.
have hd : 0<d%:E by rewrite lte_fin.
have hh : t%:E*d%:E<real_metric_ball_density hp mu a r*d%:E.
  by rewrite lte_pmul2r ?fin_numE.
rewrite /real_metric_ball_density inver (gt_eqF hdpos) -muleA -!EFinM
  mulVf ?gt_eqF // mule1 in hh.
exact hh.
Qed.
