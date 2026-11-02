(** Federer (1969), 2.2.11, p. 68: sealed witness for the universal
    closed-set construction and its countable-base background. Only the
    abstract laws are exposed; the enumeration or coding witness remains
    private. Source context and the explicit empty-base convention:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP ProductCountableBaseConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ProductCountableBaseSignature.
(** Source for [value]: abstract witness supporting the universal
    closed-set argument in Federer 2.2.11, p. 68. *)
Parameter value : forall (T V : topologicalType) (U : nat -> set T) (W : nat -> set V)
    (hU : is_countable_open_base U) (hW : is_countable_open_base W), nat -> set (T * V).
(** Source for [laws]: the witness satisfies its specification for
    Federer 2.2.11, p. 68; its construction is not exposed. *)
Parameter laws : forall (T V : topologicalType) (U : nat -> set T) (W : nat -> set V)
    (hU : is_countable_open_base U) (hW : is_countable_open_base W), is_countable_open_base (@value T V U W hU hW).
End ProductCountableBaseSignature.
Module ProductCountableBase : ProductCountableBaseSignature.
(** Source for [value]: private selection from proved existence
    for the construction in Federer 2.2.11, p. 68. *)
Definition value (T V : topologicalType) (U : nat -> set T) (W : nat -> set V)
    (hU : is_countable_open_base U) (hW : is_countable_open_base W) := projT1 (cid (@product_countable_open_base_exists T V U W hU hW)).
(** Source for [laws]: the privately selected witness discharges
    the abstract laws for Federer 2.2.11, p. 68. *)
Lemma laws (T V : topologicalType) (U : nat -> set T) (W : nat -> set V)
    (hU : is_countable_open_base U) (hW : is_countable_open_base W) : is_countable_open_base (@value T V U W hU hW).
Proof. exact: projT2 (cid (@product_countable_open_base_exists T V U W hU hW)). Qed.
End ProductCountableBase.
