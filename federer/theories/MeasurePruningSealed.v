(** Federer (1969), 2.2.12, p. 69: opaque interface for the proved
    measure-controlled coordinate choices. Subsequent proofs use only the
    recursion and loss laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace MeasureUP RegularMeasureUP
  MeasurePruningUP MeasurePruningConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type MeasurePruningSignature.
(** Source for [value]: abstract coordinate bounds and witnesses
    in Federer 2.2.12, p. 69, with finite total measure
    and positive error as in the printed proof. *)
Parameter value : forall (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R), is_measure gamma -> is_regular_measure gamma ->
    gamma setT < +oo -> forall (delta : R), (0 < delta)%R ->
    set (X * positive_sequence_space R) ->
    (nat -> nat) * (nat -> set (X * positive_sequence_space R)).
(** Source for [laws]: the abstract choices satisfy the proved
    recursion and small-loss specification of Federer 2.2.12, p. 69. *)
Parameter laws : forall (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (hm : is_measure gamma) (hr : is_regular_measure gamma)
    (ht : gamma setT < +oo) (delta : R) (hd : (0 < delta)%R)
    (Z : set (X * positive_sequence_space R)),
    is_measure_coordinate_pruning gamma Z delta
      (@value R X gamma hm hr ht delta hd Z).1
      (@value R X gamma hm hr ht delta hd Z).2.
End MeasurePruningSignature.

Module MeasurePruning : MeasurePruningSignature.
(** Source for [value]: private selection of the existence
    witness for the inductive choices in Federer 2.2.12, p. 69. *)
Definition value (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (hm : is_measure gamma) (hr : is_regular_measure gamma)
    (ht : gamma setT < +oo) (delta : R) (hd : (0 < delta)%R)
    (Z : set (X * positive_sequence_space R)) :=
  let b := cid (@measure_coordinate_pruning_exists R X gamma hm hr ht delta hd Z) in
  let F := cid (projT2 b) in (projT1 b, projT1 F).
(** Source for [laws]: the selected witnesses satisfy the
    abstract specification for Federer 2.2.12, p. 69. *)
Lemma laws (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (hm : is_measure gamma) (hr : is_regular_measure gamma)
    (ht : gamma setT < +oo) (delta : R) (hd : (0 < delta)%R)
    (Z : set (X * positive_sequence_space R)) :
    is_measure_coordinate_pruning gamma Z delta
      (@value R X gamma hm hr ht delta hd Z).1
      (@value R X gamma hm hr ht delta hd Z).2.
Proof.
exact: projT2 (cid (projT2 (cid (@measure_coordinate_pruning_exists R X gamma hm hr ht delta hd Z)))).
Qed.
End MeasurePruning.
