(** Supporting Federer (1969), 3.2.45, p. 280:
    the original orthogonal projection contracts the original diameter
    and its Hausdorff power cost. Retain zero degree and zero diameter. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric MetricDiameterUP MetricDiameter
  HausdorffDiameterCost ExtendedSupremumPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_projection_diameter_contraction]: supporting
    degree comparison in Federer 3.2.45, p. 280. Expose the actual
    diameter inequality already used to prove boundedness of projected
    bodies in 3.2.35, pp. 271–272. *)
Lemma euclidean_projection_diameter_contraction (R:realType) n k
    (p:orthogonal_projection_metric_space R n k)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  @extended_metric_diameter R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]
    (euclidean_projection_linear p @` S)<=extended_metric_diameter S.
Proof.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y:=[the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
pose D:=@extended_metric_diameter R X S.
have hD:=@extended_metric_diameter_specification R X S.
apply:(@metric_diameter_least R Y (euclidean_projection_linear p @` S) _
  (@extended_metric_diameter_specification R Y (euclidean_projection_linear p @` S)) D
  (metric_diameter_nonnegative hD)).
move=>u v [x hx <-] [y hy <-].
apply:(le_trans _ (@metric_diameter_upper R X S D hD x y hx hy)).
rewrite lee_fin;exact:euclidean_projection_nonexpanding.
Qed.

(** Source for [euclidean_projection_diameter_cost_contraction]:
    supporting the original degree-drop estimate in Federer 3.2.45,
    p. 280. The original diameter power contracts in every natural
    degree; no boundedness or measurability assumption is needed. *)
Lemma euclidean_projection_diameter_cost_contraction (R:realType) n k r
    (p:orthogonal_projection_metric_space R n k)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  @hausdorff_diameter_cost R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)] r
    (euclidean_projection_linear p @` S)<=hausdorff_diameter_cost r S.
Proof.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
apply:lee_wpmul2l;first by rewrite lee_fin;exact:ltW (hausdorff_normalisation_positive R r).
exact:nonnegative_extended_power_monotone
  (metric_diameter_nonnegative (@extended_metric_diameter_specification R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]
    (euclidean_projection_linear p @` S)))
  (euclidean_projection_diameter_contraction p S).
Qed.
