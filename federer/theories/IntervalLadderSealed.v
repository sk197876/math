(** Federer (1969), 2.2.9, p. 65: sealed scalar ladder supporting interval
    refinements with countable loss. The reciprocal construction is hidden
    behind its proved laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import IntervalLadderUP IntervalLadderConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type IntervalLadderSignature.
(** Source for [value]: supporting ladder for the interval
    choice in Federer 2.2.9, p. 65, for positive half-length
    and diameter tolerance. *)
Parameter value : forall (R : realType) (h e : R), 0 < h -> 0 < e -> nat -> R.
(** Source for [laws]: supporting positive, decreasing and
    small-gap ladder laws for Federer 2.2.9, p. 65. *)
Parameter laws : forall (R : realType) (h e : R) (hh : 0 < h) (he : 0 < e),
  is_small_interval_ladder h e (@value R h e hh he).
End IntervalLadderSignature.
Module IntervalLadder : IntervalLadderSignature.
(** Source for [value]: supporting witness selection for
    Federer 2.2.9, p. 65, from the proved ladder existence. *)
Definition value (R : realType) (h e : R) (hh : 0 < h) (he : 0 < e) :=
  projT1 (cid (small_interval_ladder_exists hh he)).
(** Source for [laws]: the selected witness satisfies the
    abstract ladder specification supporting Federer 2.2.9, p. 65. *)
Lemma laws (R : realType) (h e : R) (hh : 0 < h) (he : 0 < e) :
  is_small_interval_ladder h e (@value R h e hh he).
Proof. exact: projT2 (cid (small_interval_ladder_exists hh he)). Qed.
End IntervalLadder.
