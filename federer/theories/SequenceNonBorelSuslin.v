(** Federer (1969), 2.2.11, p. 68: existence of a Suslin non-Borel subset of
    the sequence space. The proof combines sealed countable bases and the
    universal Suslin relation with the abstract diagonal contradiction.
    Source context and base convention: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace CountableOpenBaseUP SequenceCountableBaseSealed
  ProductCountableBaseSealed UniversalSuslinSetUP UniversalSuslinSetSealed
  UniversalSuslinDiagonal SuslinSetUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sequence_universal_suslin_set_exists]: supporting
    universal Suslin relation for Y=N in Federer 2.2.11,
    p. 68. The product base is obtained from the two
    sealed countable bases, not assumed without proof. *)
Theorem sequence_universal_suslin_set_exists (R : realType) :
  exists S : set (positive_sequence_space R * positive_sequence_space R),
    is_universal_suslin_set S.
Proof.
pose N := [the topologicalType of positive_sequence_space R].
pose U := @SequenceCountableBase.value R.
have hU : is_countable_open_base U := @SequenceCountableBase.laws R.
pose V := @ProductCountableBase.value N N U U hU hU.
have hV : is_countable_open_base V := @ProductCountableBase.laws N N U U hU hU.
exists (@UniversalSuslinSet.value R N V hV); exact: UniversalSuslinSet.laws.
Qed.

(** Source for [sequence_suslin_non_borel_exists]: direct non-Borel example
    in Federer 2.2.11, p. 68: the diagonal is Suslin, its complement is not
    Suslin, and hence the diagonal is not Borel. *)
Theorem sequence_suslin_non_borel_exists (R : realType) :
  exists A : set (positive_sequence_space R),
    is_suslin_set R A /\ ~ is_suslin_set R (~` A) /\ ~ borel_set A.
Proof.
have [S hS] := sequence_universal_suslin_set_exists R.
exists (universal_suslin_diagonal S); split; first exact: universal_suslin_diagonal_suslin hS.
split; [exact: universal_suslin_diagonal_complement_not_suslin hS|
        exact: universal_suslin_diagonal_not_borel hS].
Qed.
