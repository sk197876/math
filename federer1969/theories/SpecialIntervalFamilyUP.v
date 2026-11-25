(** Federer (1969), 2.10.28, pp. 191–192: special finite interval families
    and their successive refinements. Use the actual compact interval sets
    and finite unordered families; introduce no enumeration or construction
    as a defining hypothesis. The initial family in (3) has one member, as
    corrected in Federer's erratum p. 4, book p. 192 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_special_interval_family]: direct
    definition of H special for J in
    2.10.28, p. 191: finite disjoint
    subintervals, exact total cost, and the
    bound for all subfamilies lying in a
    test interval. Finiteness is recorded by
    the finite-family type, with no chosen order. *)
Record is_special_interval_family (R : realType) (h : R -> R)
    (J : compact_real_intervals R) (H : {fset compact_real_intervals R}) : Prop := {
  (** Source for [special_interval_subsets]: direct
      S subset J condition for members of H
      in the definition, 2.10.28, p. 191. *)
  special_interval_subsets : forall S, S \in H -> val S `<=` val J;
  (** Source for [special_intervals_disjoint]: direct
      disjointness of H in 2.10.28, p. 191,
      including boundary points of closed intervals. *)
  special_intervals_disjoint : forall S T, S \in H -> T \in H -> S!=T -> val S `&` val T=set0;
  (** Source for [special_interval_cost_sum]: direct
      zeta(J)=sum zeta(S) in the definition
      of special, 2.10.28, p. 191. *)
  special_interval_cost_sum : concave_interval_cost h (val J)=
    \sum_(S <- H) concave_interval_cost h (val S);
  (** Source for [special_interval_envelope]: direct
      test-interval bound in the definition of
      special, 2.10.28, p. 191. The
      sum is over those members of H
      contained in the test interval. *)
  special_interval_envelope : forall T : compact_real_intervals R,
    \sum_(S <- H | `[< val S `<=` val T >]) concave_interval_cost h (val S)<=
      concave_interval_cost h (val T)
}.

(** Source for [special_interval_restriction]: direct
    family H intersect {T:T subset S}
    in 2.10.28(3), p. 192. It is
    a restriction of a finite family, using
    only its sets and the subset relation. *)
Definition special_interval_restriction (R : realType)
    (H : {fset compact_real_intervals R}) (A : set (real_line_metric R)) :=
  [fset S in H | `[< val S `<=` A >]].

(** Source for [is_special_interval_tree]: direct
    hypotheses in 2.10.28(3), p. 192,
    with the single-root correction in erratum
    p. 4, book p. 192 line 4.
    Express the mesh tending to zero by its
    uniform eventual diameter bound. *)
Record is_special_interval_tree (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) : Prop := {
  (** Source for [special_tree_single_root]: corrected card(H_0)=1 in
    2.10.28(3), erratum p. 4, book p. 192 line 4 *)
  special_tree_single_root : exists J, H 0%N=[fset J];
  (** Source for [special_tree_disjoint]: direct
      disjointness at every finite level in
      2.10.28(3), p. 192. *)
  special_tree_disjoint : forall j S T, S \in H j -> T \in H j -> S!=T -> val S `&` val T=set0;
  (** Source for [special_tree_refinement]: direct
      containment of every child in a parent
      in 2.10.28(3), p. 192. *)
  special_tree_refinement : forall j S, S \in H j.+1 -> exists T, T \in H j /\ val S `<=` val T;
  (** Source for [special_tree_children]: direct
      special-subfamily condition in 2.10.28(3),
      p. 192, for each parent S. *)
  special_tree_children : forall j S, S \in H j ->
    is_special_interval_family h S (special_interval_restriction (H j.+1) (val S));
  (** Source for [special_tree_mesh]: direct
      maximum diameter tending to zero in
      2.10.28(3), p. 192. The eventual
      bound also covers empty finite levels. *)
  special_tree_mesh : forall e : R, 0<e -> exists N, forall j, (N<=j)%N ->
    forall S, S \in H j -> fine (@MetricDiameter.extended_metric_diameter R
      [the metricType R of real_line_metric R] (val S))<=e
}.

(** Source for [is_special_interval_tree_limit]: direct
    A=intersection of the unions of H_j in
    2.10.28(3), p. 192, as pointwise
    membership laws before choosing a set witness. *)
Definition is_special_interval_tree_limit (R : realType)
    (H : nat -> {fset compact_real_intervals R}) (A : set (real_line_metric R)) :=
  forall x, A x <-> forall j, exists S, S \in H j /\ val S x.
