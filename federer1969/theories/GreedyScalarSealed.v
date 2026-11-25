(** Federer (1969), 2.3.3, p. 76: sealed greedy scalar partial sums. Only
    the zero/step laws are exposed. Source context and domain conventions:
    GreedyScalarExpansionUP.v. *)
From mathcomp Require Import all_boot boolp reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP GreedyScalarConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type GreedyScalarSignature.
(** Source for [value]: abstract partial sums in the proof
    of Federer 2.3.3, p. 76. *)
Parameter value : forall (R : realType) (r : nat -> R) (t : \bar R), nat -> R.
(** Source for [laws]: the zero/step laws of the recursion
    in Federer 2.3.3, p. 76. *)
Parameter laws : forall (R : realType) (r : nat -> R) (t : \bar R),
  is_greedy_scalar_expansion r t (@value R r t).
End GreedyScalarSignature.
Module GreedyScalar : GreedyScalarSignature.
(** Source for [value]: private witness choice for the greedy
    partial sums of Federer 2.3.3, p. 76. *)
Definition value (R : realType) (r : nat -> R) (t : \bar R) :=
  projT1 (cid (@greedy_scalar_exists R r t)).
(** Source for [laws]: the chosen witness satisfies the abstract
    greedy recurrence of Federer 2.3.3, p. 76. *)
Lemma laws (R : realType) (r : nat -> R) (t : \bar R) :
  is_greedy_scalar_expansion r t (@value R r t).
Proof. exact: projT2 (cid (@greedy_scalar_exists R r t)). Qed.
End GreedyScalar.
