(** Federer (1969), 2.2.1, p. 60: support of a measure on a topological
    space. The abstract specification is closedness and the neighborhood
    characterisation of the printed complement of the union of open null
    sets. it is not a separate general support definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_support]: Federer 2.2.1, p. 60,
    definition, paraphrased: the support is closed and a point lies
    in it exactly when no open neighborhood of that point has zero
    measure. This specifies the object by its laws before constructing
    the printed complement of a union. *)
Record is_measure_support (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (S : set T) := {
  measure_support_closed_law : closed S;
  measure_support_neighborhood_law : forall x, S x <->
    forall U, open U -> U x -> mu U <> 0
}.

(** Source for [measure_support_unique]: Federer 2.2.1,
    p. 60, supporting uniqueness from the defining open-null-set
    complement, expressed through the neighborhood specification. *)
Lemma measure_support_unique (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (S Q : set T) :
  is_measure_support mu S -> is_measure_support mu Q -> S = Q.
Proof.
move=> hS hQ; apply/seteqP; split=> x hx.
- apply: (proj2 (measure_support_neighborhood_law hQ x)).
  exact: (proj1 (measure_support_neighborhood_law hS x) hx).
- apply: (proj2 (measure_support_neighborhood_law hS x)).
  exact: (proj1 (measure_support_neighborhood_law hQ x) hx).
Qed.
