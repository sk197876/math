(** Federer (1969), 3.2.46, p. 281: the real-degree Hausdorff
    comparison follows from the local distance comparison. Supporting
    positive-bound image estimate from 2.10.11, p. 176, proved directly
    for the real-power covering laws, without a multiplicity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealPower ExtendedPositivePower MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasure MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffLengthMaps HausdorffLipschitzCost LipschitzUP
  LipschitzCaratheodoryTransport RealHausdorffNormalisation RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_real_power_positive_scale]: the
    lambda^m scaling of actual diameter costs, supporting Federer
    3.2.46, p. 281, the first Hausdorff comparison. Zero diameter,
    exponent zero and infinite diameter are explicitly retained. *)
Lemma extended_metric_real_power_positive_scale (R : realType)
    (L p : R) (d : \bar R) :
  (0 < L)%R -> 0 <= d ->
  extended_metric_real_power (L%:E*d) p =
    (real_power L p)%:E*extended_metric_real_power d p.
Proof.
move=> hL hd; case: (eqVneq p 0%R)=> [->|hp].
- by rewrite /extended_metric_real_power eqxx real_power_zero_exponent mul1e.
rewrite /extended_metric_real_power (negPf hp).
case: d hd=> [d hd|_|hd].
- have hdR : (0 <= d)%R by move: hd; rewrite lee_fin.
  by rewrite -EFinM /extended_positive_power /=
    (@real_power_product R L d p (ltW hL) hdR) -EFinM.
- rewrite gt0_muley; last by rewrite lte_fin.
  rewrite /extended_positive_power; apply: esym; apply: gt0_muley.
  rewrite lte_fin; exact: (@real_power_strictly_positive R L p hL).
- by rewrite leeNy_eq in hd.
Qed.

(** Source for [metric_real_power_positive_lipschitz]: the
    positive finite Lipschitz-bound real-degree image estimate
    used in Federer 3.2.46, p. 281. It concerns actual original
    sets, with no measurability, completeness or finiteness premise. *)
Theorem metric_real_power_positive_lipschitz (R : realType)
    (X Y : metricType R) (f : X -> Y) (L c p : R) :
  (0 < L)%R -> (0 <= c)%R -> (0 <= p)%R ->
  is_metric_lipschitz_bound setT f L -> forall A,
  @metric_real_power_measure R Y c p (f @` A) <=
    (real_power L p)%:E * @metric_real_power_measure R X c p A.
Proof.
move=> hL hc hp hf A.
refine (@lipschitz_caratheodory_transport R X Y
  (@nonempty_metric_sets R X) (@nonempty_metric_sets R Y)
  (fun j => val j) (fun j => val j)
  (fun j => metric_real_diameter_cost c p (val j))
  (fun j => metric_real_diameter_cost c p (val j))
  f (@nonempty_metric_image R X Y f)
  (@metric_real_power_measure R X c p) (@metric_real_power_measure R Y c p)
  L (real_power L p)
  (@metric_real_power_measure_specification R X c p)
  (@metric_real_power_measure_specification R Y c p)
  (fun j => @metric_real_power_cost_nonnegative R c p (extended_metric_diameter (val j)) hc) hL
  (@real_power_strictly_positive R L p hL) _ _ _ A).
- move=> j x hx; by exists x.
- move=> j; exact: extended_metric_diameter_lipschitz hf (val j).
- move=> j.
  have hD := extended_metric_diameter_lipschitz hf (val j).
  have hNonneg := metric_diameter_nonnegative
    (extended_metric_diameter_specification (val j)).
  have hImageNonneg := metric_diameter_nonnegative
    (extended_metric_diameter_specification (val (nonempty_metric_image f j))).
  apply: le_trans (metric_real_power_cost_monotone hc hp hImageNonneg hD) _.
  rewrite /metric_real_power_cost extended_metric_real_power_positive_scale //.
  by rewrite muleCA.
Qed.

(** Source for [real_hausdorff_positive_lipschitz]: actual
    Gamma-normalized real-dimensional specialization of the image
    comparison needed in Federer 3.2.46, p. 281. Every p>=0 remains. *)
Theorem real_hausdorff_positive_lipschitz (R : realType)
    (X Y : metricType R) (f : X -> Y) (L p : R) (hp : (0 <= p)%R) :
  (0 < L)%R -> is_metric_lipschitz_bound setT f L -> forall A,
  @real_hausdorff_measure R Y p hp (f @` A) <=
    (real_power L p)%:E * @real_hausdorff_measure R X p hp A.
Proof.
move=> hL hf.
exact: (@metric_real_power_positive_lipschitz R X Y f L
  (real_hausdorff_normalisation hp) p hL
  (ltW (real_hausdorff_normalisation_positive hp)) hp hf).
Qed.
