(** Federer (1969), 2.2.5, pp. 62-63: Radon measures on locally compact
    Hausdorff spaces. Measure laws are separate; compactness and separation
    are general-topology background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_radon_measure]: Federer 2.2.5, p. 62, definition. The
    record retains the locally compact Hausdorff ambient hypothesis and
    compact finiteness. Inner regularity on open sets and outer regularity
    on all sets are specified by the extremal order laws; their
    complementary bounds follow from monotonicity. *)
Record is_radon_measure (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : Prop := {
  radon_hausdorff : @hausdorff_space T;
  radon_locally_compact : locally_compact (@setT T);
  radon_compact_finite : forall K, compact K -> mu K < +oo;
  radon_open_measurable : forall V, open V -> measure_measurable mu V;
  radon_inner_least : forall V, open V -> forall c,
    (forall K, compact K -> K `<=` V -> mu K <= c) -> mu V <= c;
  radon_outer_greatest : forall A c,
    (forall V, open V -> A `<=` V -> c <= mu V) -> c <= mu A
}.
