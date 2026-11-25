(** Federer (1969), 3.4.8(2), p. 326:
    depth is the least index for which the original
    directional reduction sets have a common element.
    The laws assert no Haar or dimension conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [has_analytic_reduction_tail]: the nonempty
    intersection of B_j for j>m, 3.4.8(2), p. 326.
    Array index j denotes the printed index j+1. *)
Definition has_analytic_reduction_tail n (O:Type) (B:'I_n->set O) m:Prop:=
  exists g,forall j:'I_n,(m<=j)%N ->B j g.

(** Source for [is_analytic_reduction_depth]: the original
    infimum in 3.4.8(2), p. 326, specified independently
    by attainment and minimality, including n=0. *)
Record is_analytic_reduction_depth n (O:Type) (B:'I_n->set O) (d:nat):Prop:={
  (** Source for [analytic_reduction_depth_bound]: depth lies
      between zero and n, 3.4.8(2), p. 326. *)
  analytic_reduction_depth_bound:(d<=n)%N;
  (** Source for [analytic_reduction_depth_attained]: the
      original intersection at depth is nonempty,
      3.4.8(2), p. 326. *)
  analytic_reduction_depth_attained:has_analytic_reduction_tail B d;
  (** Source for [analytic_reduction_depth_minimal]: no smaller
      index has a nonempty original intersection,
      3.4.8(2), p. 326. *)
  analytic_reduction_depth_minimal:forall m,has_analytic_reduction_tail B m ->(d<=m)%N
}.
