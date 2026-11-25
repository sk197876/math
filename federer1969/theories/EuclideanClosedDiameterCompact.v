(** Supporting bounded compactness for the closed convex generator family of
    Federer (1969), 2.10.4(2), p. 172. A closed Euclidean generator at a
    finite diameter cutoff is compact. This is the bounded compactness of
    1.7.1, p. 28; retain the empty-set case rather than assuming a source
    point. Source context and the nonempty argument:
    EuclideanBoundedClosure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricDiameter EuclideanBoundedClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_finite_diameter_compact]:
    supporting compact generators at finite cutoffs in
    Federer 2.10.4(2), p. 172, from Euclidean
    bounded compactness, including empty generators. *)
Theorem euclidean_closed_finite_diameter_compact (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d : R) :
  closed A -> (extended_metric_diameter A<=d%:E)%E -> compact A.
Proof.
move=> hc hd; case: (pselect (A !=set0))=> [hne|hno].
- rewrite (proj1 (closure_id A) hc); exact: euclidean_bounded_set_closure_compact hne hd.
- have he : A=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hno; by exists x.
  rewrite he; exact: compact0.
Qed.
