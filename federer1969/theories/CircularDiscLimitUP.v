(** Federer (1969), 3.3.19, p. 302: independently
    specify the original intersection of level unions.
    No compactness, measure, projection or density conclusion
    is built into the definition. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [circular_disc_level_union]: the original
    union of closed discs in G_n, 3.3.19, p. 302. *)
Definition circular_disc_level_union (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)}) j:=
  [set x|exists z,z \in H j /\metric_closed_ball z (@FactorialDiscScales.radius R j) x].

(** Source for [is_circular_disc_limit]: literal pointwise
    membership in A=intersection union G_n of 3.3.19,
    p. 302. Adding the original unit root leaves this
    intersection unchanged by the proved child containment. *)
Definition is_circular_disc_limit (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)})
    (A:set (inner_metric_space (@euclidean_inner_productP R 2))):Prop:=
  forall x,A x <->forall j,circular_disc_level_union H j x.
