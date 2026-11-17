(** Supporting Federer (1969), 3.2.45, p. 280:
    the unit ball lies in the coordinate cube, so the original
    Hausdorff diameter coefficient is at most one in every natural degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology EuclideanBallBoxBound HausdorffDiameterCost MetricDiameterUP MetricDiameter ExtendedSupremumPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_normalisation_le_one]: supporting the
    original degree-drop estimate of Federer 3.2.45, p. 280. The
    original coefficient alpha(r)2^(-r) is at most one, including r=0. *)
Lemma hausdorff_normalisation_le_one (R:realType) r:(hausdorff_normalisation R r<=1)%R.
Proof.
have hPositive:(0<(2:R)^+r)%R by rewrite exprn_gt0 // ltr0n.
rewrite /hausdorff_normalisation ler_pdivrMr // mul1r.
exact:euclidean_unit_ball_box_bound.
Qed.

(** Source for [hausdorff_diameter_cost_below_power]: supporting
    the original degree-drop estimate of Federer 3.2.45, p. 280.
    Retain both zero-diameter and zero-degree conventions; the
    auxiliary numerical cost is also defined on the empty set. *)
Lemma hausdorff_diameter_cost_below_power (R:realType) (X:metricType R) r (S:set X):
  hausdorff_diameter_cost r S<=(extended_metric_diameter S)^+r.
Proof.
have hPower:(0<=(extended_metric_diameter S)^+r)%E.
  apply:expe_ge0;exact:metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hCoefficient : ((hausdorff_normalisation R r)%:E <= (1 : \bar R))%E.
  rewrite lee_fin;exact:hausdorff_normalisation_le_one.
have hBound:=lee_wpmul2r hPower hCoefficient.
by rewrite mul1e in hBound.
Qed.
