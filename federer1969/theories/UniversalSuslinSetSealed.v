(** Federer (1969), 2.2.11, p. 68: sealed universal Suslin set obtained from
    the universal closed set for the product. Its abstract laws contain the
    corrected ambient product of erratum p. 1, book p. 68 line 14. Source
    context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP UniversalClosedSetUP
  UniversalClosedSetSealed UniversalSuslinSetUP UniversalSuslinConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type UniversalSuslinSetSignature.
(** Source for [value]: abstract universal Suslin witness in
    Federer 2.2.11, p. 68, for a supplied product base. *)
Parameter value : forall (R : realType) (T : topologicalType)
  (U : nat -> set (T * positive_sequence_space R)), is_countable_open_base U ->
  set (T * positive_sequence_space R).
(** Source for [laws]: the witness is Suslin and contains every
    Suslin subset as a slice, as in Federer 2.2.11, p. 68. *)
Parameter laws : forall (R : realType) (T : topologicalType)
  (U : nat -> set (T * positive_sequence_space R)) (hU : is_countable_open_base U),
  is_universal_suslin_set (@value R T U hU).
End UniversalSuslinSetSignature.
Module UniversalSuslinSet : UniversalSuslinSetSignature.
(** Source for [value]: private projection witness for the
    universal S in Federer 2.2.11, p. 68. *)
Definition value (R : realType) (T : topologicalType)
    (U : nat -> set (T * positive_sequence_space R)) (hU : is_countable_open_base U) :=
  @universal_suslin_relation R T
    (@UniversalClosedSet.value R [the topologicalType of (T * positive_sequence_space R)%type] U hU).
(** Source for [laws]: the private witness satisfies the universal
    Suslin-set laws of Federer 2.2.11, p. 68. *)
Lemma laws (R : realType) (T : topologicalType)
    (U : nat -> set (T * positive_sequence_space R)) (hU : is_countable_open_base U) :
  is_universal_suslin_set (@value R T U hU).
Proof.
apply: universal_suslin_relation_laws; exact: UniversalClosedSet.laws.
Qed.
End UniversalSuslinSet.
