(** Federer (1969), 2.10.35, p. 197: each equal-dimension orthogonal
    projection preserves actual Lebesgue measure, hence its projected-
    volume supremum is exactly Lebesgue measure. This supports the Gross and
    convex Caratheodory comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ProjectedVolumeGauge FullDimensionProjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [equal_dimension_projected_volume_gauge]: supporting
    equal-dimension projected cost in the
    measure comparisons of 2.10.35, p. 197.
    Supremum attainment is unnecessary; existence
    of one projection suffices for the lower bound. *)
Theorem equal_dimension_projected_volume_gauge (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  projected_volume_gauge n S=euclidean_lebesgue_measure n S.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: projected_volume_gauge_least_bound=> p hp.
  by rewrite (equal_dimension_projection_volume S hp).
- have [p hp] := @euclidean_projection_exists R n n (leqnn n).
  have hh := projected_volume_gauge_projection_bound S hp.
  by rewrite (equal_dimension_projection_volume S hp) in hh.
Qed.
