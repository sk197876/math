(** Federer (1969), 2.10.46, p. 203: fix the second factor and apply
    covering inequalities on the first. As for gamma in 2.10.45, p. 202,
    restriction and image measure give an outer measure even when the fixed
    factor is not measurable. Source context: MetricRectangleSliceMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricProductRectangles MeasureUP MeasureRestriction MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_rectangle_first_slice_is_measure]: supporting
    first-factor measure in the double covering step of 2.10.46,
    p. 203, using the operations of 2.1.2, p. 54. *)
Lemma metric_rectangle_first_slice_is_measure (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (T : set Y) (mu : set P -> \bar R) :
  is_measure mu -> is_measure (fun S=>mu (metric_product_rectangle first second S T)).
Proof.
move=> hm.
have he : (fun S=>mu (metric_product_rectangle first second S T))=
  measure_pushforward first (measure_restrict mu (second @^-1` T)).
  by apply: funext=> S; rewrite /measure_pushforward /measure_restrict /metric_product_rectangle setIC.
rewrite he; exact: measure_pushforward_is_measure (measure_restrict_is_measure hm _).
Qed.
