(** Proved enlargement witness for Federer (1969), 2.10.24, p. 188, using
    the closure convention of 2.10.2(1), p. 171, and the diameter
    enlargement of 2.10.18, p. 180. The downstream equality argument will
    use only the sealed weak enlargement laws. No bounded compactness is
    needed for this closed-generator witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter MetricDiameterClosure DiameterEnlargements
  CaratheodoryEnlargementGrowth CaratheodoryWeakEnlargementUP HausdorffDiameterCost
  HausdorffPowerCostLaws HausdorffLipschitzCost ClosedHausdorffEnlargementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_hausdorff_enlargement_exists]: supporting
    existence proof for the Hausdorff application of
    2.10.24, p. 188. Closure preserves diameter
    and the gauge, while the five-diameter estimate
    controls the natural power. Nonempty zero-diameter
    sets, zero costs and unbounded generators remain allowed. *)
Theorem closed_hausdorff_enlargement_exists (R : realType) (X : metricType R) (m : nat) :
  exists E : set X -> set X,
    is_weak_caratheodory_enlargement [set S : set X | closed S /\ S!=set0]
      (@hausdorff_diameter_cost R X m) E (closed_hausdorff_enlargement_control R m).
Proof.
pose F := [set S : set X | closed S /\ S!=set0].
pose E (S : set X) := closure (diameter_enlargement F S).
pose k := closed_hausdorff_enlargement_control R m.
have hk := @closed_hausdorff_enlargement_control_bounds R m.
have hcontains S (hS : F S) : S `<=` E S.
  move=> x hx; apply: subset_closure; exact: (@diameter_enlargement_contains R X F S hS x hx).
have hdiam S : extended_metric_diameter (E S)<=5%:E*extended_metric_diameter S.
  rewrite /E extended_metric_diameter_closure; exact: diameter_enlargement_scaled_bound F S.
have hcost S : hausdorff_diameter_cost m (E S)<=((5:R)^+m)%R%:E*hausdorff_diameter_cost m S.
  have hh := @hausdorff_power_cost_monotone R m _ _
    (metric_diameter_nonnegative (extended_metric_diameter_specification (E S))) (hdiam S).
  rewrite /hausdorff_diameter_cost; apply: le_trans hh _.
  by rewrite /hausdorff_power_cost extended_natural_power_scale muleCA.
exists E; constructor.
- exact hk.1.
- move=> S hS; exact: hausdorff_diameter_cost_nonnegative.
- move=> S hS; split; first exact: (@closed_closure X (diameter_enlargement F S)).
  have [x hx] := hS.2; exists x; exact: hcontains S hS x hx.
- by move=> S hS x hx; exact: subset_closure hx.
- move=> S hS; apply: le_trans (hdiam S) _.
  apply: lee_wpmul2r; first exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
  by rewrite lee_fin; exact hk.2.1.
- move=> S hS; apply: le_trans (hcost S) _.
  apply: lee_wpmul2r; first exact: hausdorff_diameter_cost_nonnegative.
  by rewrite lee_fin; exact hk.2.2.
Qed.
