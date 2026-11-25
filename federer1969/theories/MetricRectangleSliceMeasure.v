(** Federer (1969), 2.10.45, pp. 202–203: rectangle sections give measures
    on either factor. This supporting form applies also to a size-cutoff
    approximation before passing to Hausdorff measure. Restriction and image
    are those of 2.1.2, p. 54. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricProductRectangles MeasureUP MeasureRestriction MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_rectangle_second_slice_is_measure]: supporting
    second-factor measure needed to take the covering infimum
    in 2.10.45, p. 203. Neither the fixed first-factor
    set nor the varying second-factor set must be measurable. *)
Theorem metric_rectangle_second_slice_is_measure (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (Q : set X) (nu : set P -> \bar R) :
  is_measure nu -> is_measure (fun T=>nu (metric_product_rectangle first second Q T)).
Proof.
move=> hn.
have he : (fun T=>nu (metric_product_rectangle first second Q T))=
    measure_pushforward second (measure_restrict nu (first @^-1` Q)).
  by apply: funext=> T; rewrite /metric_product_rectangle /measure_pushforward /measure_restrict.
rewrite he.
exact: measure_pushforward_is_measure (measure_restrict_is_measure hn _).
Qed.
