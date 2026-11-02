(** Integer-degree image estimate supporting Federer (1969), 2.10.11, p.
    176. Scaled image covers prove the Lipschitz bound on Hausdorff measure
    for arbitrary targets. The zero Lipschitz constant is treated
    explicitly: positive degrees give a singleton image, while degree zero
    keeps 0^0=1. The multiplicity inequality and optional real-degree
    extension are separate obligations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import LipschitzUP LipschitzBasic LipschitzCaratheodoryTransport
  MetricDiameter HausdorffLengthUP HausdorffLengthMaps HausdorffDiameterCost HausdorffLipschitzCost
  HausdorffMeasureUP HausdorffMeasure HausdorffCountableNull MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_positive_lipschitz_image_bound]: supporting
    positive-constant, integer-degree image-cover estimate for
    Federer 2.10.11, p. 176. Completeness, separability and
    target measurability are not needed for this estimate. *)
Lemma hausdorff_positive_lipschitz_image_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (m : nat) :
  (0<L)%R -> is_metric_lipschitz_bound setT f L ->
  forall A, @hausdorff_measure R Y m (f @` A)<=(L^+m)%R%:E* @hausdorff_measure R X m A.
Proof.
move=> hL hf A.
refine (@lipschitz_caratheodory_transport R X Y (@nonempty_metric_sets R X) (@nonempty_metric_sets R Y)
  (fun j => val j) (fun j => val j) (fun j => hausdorff_diameter_cost m (val j))
  (fun j => hausdorff_diameter_cost m (val j)) f (@nonempty_metric_image R X Y f)
  (@hausdorff_measure R X m) (@hausdorff_measure R Y m) L (L^+m)%R
  (@hausdorff_measure_specification R X m) (@hausdorff_measure_specification R Y m)
  (fun j => hausdorff_diameter_cost_nonnegative m (val j)) hL _ _ _ _ A).
- exact: exprn_gt0 hL.
- move=> j x hx; by exists x.
- move=> j; exact: (@extended_metric_diameter_lipschitz R X Y f L hf (val j)).
- move=> j; exact: (@hausdorff_lipschitz_cost_bound R X Y f L m hf (val j)).
Qed.

(** Source for [hausdorff_lipschitz_image_bound]: direct
    integer-degree image comparison used in the proof of
    Federer 2.10.11, p. 176. Includes empty targets, zero
    Lipschitz bounds and degree zero, with 0^0=1. *)
Theorem hausdorff_lipschitz_image_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (m : nat) : is_metric_lipschitz_bound setT f L ->
  forall A, @hausdorff_measure R Y m (f @` A)<=(L^+m)%R%:E* @hausdorff_measure R X m A.
Proof.
move=> hf A; case: (ltP 0%R L)=> [hL|hL].
  exact: (@hausdorff_positive_lipschitz_image_bound R X Y f L m hL hf A).
have hz : L=0%R by apply/eqP; rewrite eq_le hL hf.1.
rewrite hz; rewrite hz in hf; case: m=> [|m].
- rewrite expr0 mul1e.
  have h1 := @metric_lipschitz_bound_increase R X Y setT f 0%R 1%R hf ler01.
  have hh := @hausdorff_positive_lipschitz_image_bound R X Y f 1%R 0 ltr01 h1 A.
  by rewrite expr0 mul1e in hh.
- rewrite exprS mul0r mul0e.
  case: (pselect (A !=set0))=> [[a ha]|hempty]; last first.
    have he : A=set0 by apply/seteqP; split=> x hx //; exfalso; apply: hempty; by exists x.
    by rewrite he image_set0 (measure_empty (@hausdorff_measure_is_measure R Y m.+1)).
  have hsub : f @` A `<=` [set f a].
    move=> y [x hx <-]; apply: (@mdist_positivity R Y (f x) (f a)).
    apply/eqP; rewrite eq_le mdist_ge0 andbT.
    by have hh := hf.2 x a I I; rewrite mul0r in hh.
  have hb := @measure_mono R Y (@hausdorff_measure R Y m.+1)
    (@hausdorff_measure_is_measure R Y m.+1) (f @` A) [set f a] hsub.
  by rewrite (@hausdorff_positive_degree_singleton_zero R Y m.+1 (f a) (ltn0Sn m)) in hb.
Qed.
