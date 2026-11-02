(** Supporting integer-degree cost comparison for Federer (1969), 2.10.11,
    p. 176. Lipschitz images multiply diameters by at most L, and the
    normalized degree-m cost by at most L^m. The integer degree, including
    degree zero, matches the existing construction of 2.10.2, p. 171. Its
    optional real-degree Gamma extension is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import LipschitzUP MetricDiameterUP MetricDiameter
  HausdorffDiameterCost HausdorffPowerCostLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_diameter_lipschitz]: supporting diameter
    estimate in the proof of Federer 2.10.11, p. 176 Zero Lipschitz bounds
    and infinite source diameters are allowed. *)
Lemma extended_metric_diameter_lipschitz (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) : is_metric_lipschitz_bound setT f L ->
  forall A, extended_metric_diameter (f @` A)<=L%:E*extended_metric_diameter A.
Proof.
move=> [hL hf] A; apply: (metric_diameter_least (extended_metric_diameter_specification (f @` A))).
- apply: mule_ge0; first exact hL.
  exact: metric_diameter_nonnegative (extended_metric_diameter_specification A).
- move=> _ _ [x hx <-] [y hy <-].
  have hd : (mdist (f x) (f y))%:E<=L%:E*(mdist x y)%:E.
    rewrite -EFinM lee_fin; exact: hf x y I I.
  apply: le_trans hd _; apply: lee_wpmul2l; first exact hL.
  exact: (@metric_diameter_upper R X A _ (extended_metric_diameter_specification A) x y hx hy).
Qed.

(** Source for [extended_natural_power_scale]: elementary
    power identity supporting the integer-degree cost estimate
    in Federer 2.10.11, p. 176. The zero degree gives one,
    including zero or infinite diameter. *)
Lemma extended_natural_power_scale (R : realType) (L : R) (d : \bar R) (m : nat) :
  (L%:E*d)^+m=(L^+m)%:E*d^+m.
Proof.
elim: m=> [|m ih]; first by rewrite !expe0 expr0 mul1e.
by rewrite !expeS exprS ih EFinM muleACA.
Qed.

(** Source for [hausdorff_lipschitz_cost_bound]: direct
    integer-degree cost inequality in the proof of Federer
    2.10.11, p. 176. It includes L=0, m=0 and infinite
    diameters with the existing zero-times-infinity convention. *)
Theorem hausdorff_lipschitz_cost_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (m : nat) : is_metric_lipschitz_bound setT f L ->
  forall A, @hausdorff_diameter_cost R Y m (f @` A)<=(L^+m)%R%:E*hausdorff_diameter_cost m A.
Proof.
move=> hL A.
apply: le_trans (@hausdorff_power_cost_monotone R m _ _
  (metric_diameter_nonnegative (extended_metric_diameter_specification (f @` A)))
  (@extended_metric_diameter_lipschitz R X Y f L hL A)) _.
by rewrite /hausdorff_power_cost /hausdorff_diameter_cost extended_natural_power_scale muleCA.
Qed.
