(** Federer (1969), 2.2.11, p. 68: sealed normalization of an enumerated
    open base to include the empty member. Source context and boundary
    clarification: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import CountableOpenBaseUP CountableBaseNormalizationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type CountableBaseNormalizationSignature.
(** Source for [value]: abstract base witness supporting the
    universal closed relation in Federer 2.2.11, p. 68. *)
Parameter value : forall (T : topologicalType) (U : nat -> set T),
  (forall i, open (U i)) ->
  (forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) -> nat -> set T.
(** Source for [laws]: the normalized base satisfies its abstract
    laws for Federer 2.2.11, p. 68, including an empty member. *)
Parameter laws : forall (T : topologicalType) (U : nat -> set T)
  (ho : forall i, open (U i))
  (hr : forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V),
  is_countable_open_base (@value T U ho hr).
End CountableBaseNormalizationSignature.
Module CountableBaseNormalization : CountableBaseNormalizationSignature.
(** Source for [value]: private selection of the normalized base
    proved to exist for Federer 2.2.11, p. 68. *)
Definition value (T : topologicalType) (U : nat -> set T)
  (ho : forall i, open (U i))
  (hr : forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) :=
  projT1 (cid (@normalized_countable_base_exists T U ho hr)).
(** Source for [laws]: the existence proof discharges the base
    specification supporting Federer 2.2.11, p. 68. *)
Lemma laws (T : topologicalType) (U : nat -> set T)
  (ho : forall i, open (U i))
  (hr : forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) :
  is_countable_open_base (@value T U ho hr).
Proof. exact: projT2 (cid (@normalized_countable_base_exists T U ho hr)). Qed.
End CountableBaseNormalization.
