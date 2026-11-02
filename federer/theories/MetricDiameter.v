(** Public diameter and order consequences supporting Federer (1969),
    2.10.1, p. 170, and 2.10.2(1), p. 171, for the example in 2.5.10, p.
    101. Source context and empty-set convention: MetricDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameterSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_metric_diameter]: the diameter used
    by Federer 2.10.1, p. 170, through its sealed laws. *)
Definition extended_metric_diameter (R : realType) (X : metricType R)
    (A : set X) := @MetricDiameter.value R X A.

(** Source for [extended_metric_diameter_specification]: the
    diameter order laws supporting Federer 2.10.1, p. 170. *)
Lemma extended_metric_diameter_specification (R : realType) (X : metricType R)
    (A : set X) : is_extended_metric_diameter A (extended_metric_diameter A).
Proof. exact: MetricDiameter.laws. Qed.

(** Source for [extended_metric_diameter_mono]: inclusion
    preserves the diameter bound in Federer 2.10.1, p. 170;
    this supporting fact compares admissible covers. *)
Lemma extended_metric_diameter_mono (R : realType) (X : metricType R)
    (A B : set X) : A `<=` B -> extended_metric_diameter A <= extended_metric_diameter B.
Proof.
move=> hAB; apply: (metric_diameter_least (extended_metric_diameter_specification A)).
- exact: metric_diameter_nonnegative (extended_metric_diameter_specification B).
- move=> x y hx hy; exact: (metric_diameter_upper
    (extended_metric_diameter_specification B) (hAB x hx) (hAB y hy)).
Qed.

(** Source for [extended_metric_diameter_empty]: explicit
    zero convention for the empty set, auxiliary to Federer
    2.10.2(1), p. 171, whose cover sets are nonempty. *)
Lemma extended_metric_diameter_empty (R : realType) (X : metricType R) :
  extended_metric_diameter (@set0 X)=0.
Proof.
apply/eqP; rewrite eq_le (metric_diameter_nonnegative
  (extended_metric_diameter_specification (@set0 X))) andbT.
apply: (metric_diameter_least (extended_metric_diameter_specification (@set0 X)))=> //.
Qed.
