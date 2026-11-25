(** Federer (1969), 2.10.23, p. 186: sealed coordinate-pruning choices with
    continuity below instead of regularity. The public laws are the existing
    recursion and geometric loss specification of 2.2.12, p. 69. Source
    context: IncreasingProjectionLoss.v. The private recursion is not
    exported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace MeasureUP MeasurePruningUP IncreasingProjectionLoss ContinuousPruningConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Module Type ContinuousPruningSignature.
(** Source for [value]: abstract coordinate bounds
    and witnesses for 2.10.23, p. 186. *)
Parameter value : forall (R : realType) (X : topologicalType) (gamma : set X -> \bar R),
  is_measure gamma -> has_increasing_set_continuity gamma ->
  forall (e : R), (0<e)%R -> forall Z : set (X*positive_sequence_space R),
    gamma (fst @` Z)< +oo -> (nat -> nat)*(nat -> set (X*positive_sequence_space R)).
(** Source for [laws]: the abstract choices satisfy
    the recursion and loss laws used in
    2.10.23, p. 186. *)
Parameter laws : forall (R : realType) (X : topologicalType) (gamma : set X -> \bar R)
  (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma)
  (e : R) (he : (0<e)%R) (Z : set (X*positive_sequence_space R)) (hf : gamma (fst @` Z)< +oo),
  is_measure_coordinate_pruning gamma Z e (@value R X gamma hm hcont e he Z hf).1
    (@value R X gamma hm hcont e he Z hf).2.
End ContinuousPruningSignature.
Module ContinuousPruning : ContinuousPruningSignature.
(** Source for [value]: selection from proved
    pruning existence for 2.10.23, p. 186. *)
Definition value (R : realType) (X : topologicalType) (gamma : set X -> \bar R)
  (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma)
  (e : R) (he : (0<e)%R) (Z : set (X*positive_sequence_space R)) (hf : gamma (fst @` Z)< +oo) :=
  let b := cid (@continuous_coordinate_pruning_exists R X gamma hm hcont e he Z hf) in
  let F := cid (projT2 b) in (projT1 b,projT1 F).
(** Source for [laws]: proved abstract recursion
    and geometric losses for 2.10.23, p. 186. *)
Lemma laws (R : realType) (X : topologicalType) (gamma : set X -> \bar R)
  (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma)
  (e : R) (he : (0<e)%R) (Z : set (X*positive_sequence_space R)) (hf : gamma (fst @` Z)< +oo) :
  is_measure_coordinate_pruning gamma Z e (@value R X gamma hm hcont e he Z hf).1
    (@value R X gamma hm hcont e he Z hf).2.
Proof. exact: projT2 (cid (projT2 (cid (@continuous_coordinate_pruning_exists R X gamma hm hcont e he Z hf)))). Qed.
End ContinuousPruning.
