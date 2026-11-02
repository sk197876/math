(** Public pruning interface for Federer (1969), 2.10.23, p. 186. Only
    sealed recursion and loss laws are visible. Source context and
    continuity premise: IncreasingProjectionLoss.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace MeasureUP MeasurePruningUP IncreasingProjectionLoss ContinuousPruningSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_coordinate_pruning]: supporting
    sealed Z_i choices in 2.10.23, p. 186. *)
Definition continuous_coordinate_pruning (R : realType) (X : topologicalType) (gamma : set X -> \bar R)
  (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma)
  (e : R) (he : (0<e)%R) (Z : set (X*positive_sequence_space R)) (hf : gamma (fst @` Z)< +oo) :=
  @ContinuousPruning.value R X gamma hm hcont e he Z hf.

(** Source for [continuous_coordinate_pruning_specification]: proved
    recursion and loss laws for the selected
    witnesses in 2.10.23, p. 186. *)
Lemma continuous_coordinate_pruning_specification (R : realType) (X : topologicalType) (gamma : set X -> \bar R)
  (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma)
  (e : R) (he : (0<e)%R) (Z : set (X*positive_sequence_space R)) (hf : gamma (fst @` Z)< +oo) :
  is_measure_coordinate_pruning gamma Z e (@continuous_coordinate_pruning R X gamma hm hcont e he Z hf).1
    (@continuous_coordinate_pruning R X gamma hm hcont e he Z hf).2.
Proof. exact: ContinuousPruning.laws. Qed.
