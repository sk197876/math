(** Federer (1969), 2.2.11, p. 68: universal closed and Suslin sets for a
    space with a countable open base. An arbitrary base is normalized behind
    a sealed interface; the public hypotheses do not require an empty base
    member. The Suslin relation has ambient space Y times N, as corrected in
    erratum p. 1, book p. 68 line 14. Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP CountableBaseNormalizationSealed
  SequenceCountableBaseSealed ProductCountableBaseSealed
  UniversalClosedSetUP UniversalClosedSetSealed UniversalSuslinSetUP UniversalSuslinSetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_universal_closed_set]: direct first
    existence assertion in Federer 2.2.11, p. 68. Any enumerated
    open base suffices: its sealed normalization adjoins the empty
    set before the universal relation is constructed. *)
Theorem countable_base_universal_closed_set (R : realType) (T : topologicalType)
    (U : nat -> set T) :
  (forall i, open (U i)) ->
  (forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) ->
  exists C, @is_universal_closed_set R T C.
Proof.
move=> ho hr; pose W := @CountableBaseNormalization.value T U ho hr.
have hW : is_countable_open_base W := @CountableBaseNormalization.laws T U ho hr.
exists (@UniversalClosedSet.value R T W hW); exact: UniversalClosedSet.laws.
Qed.

(** Source for [countable_base_universal_suslin_set]: direct second
    existence assertion in Federer 2.2.11, p. 68. Use the
    countable product base of Y times N, then project the universal
    closed relation to obtain every Suslin set as a parameter slice. *)
Theorem countable_base_universal_suslin_set (R : realType) (T : topologicalType)
    (U : nat -> set T) :
  (forall i, open (U i)) ->
  (forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) ->
  exists S, @is_universal_suslin_set R T S.
Proof.
move=> ho hr; pose W := @CountableBaseNormalization.value T U ho hr.
have hW : is_countable_open_base W := @CountableBaseNormalization.laws T U ho hr.
pose N := [the topologicalType of positive_sequence_space R].
pose V := @SequenceCountableBase.value R.
have hV : is_countable_open_base V := @SequenceCountableBase.laws R.
pose B := @ProductCountableBase.value T N W V hW hV.
have hB : is_countable_open_base B := @ProductCountableBase.laws T N W V hW hV.
exists (@UniversalSuslinSet.value R T B hB); exact: UniversalSuslinSet.laws.
Qed.
