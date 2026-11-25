(** Opaque interface for the cardinal law of Federer (1969), 2.5.11, p. 102:
    the square of a representative of aleph-one injects into the
    representative. Source context and the transfinite argument:
    AlephOneSquareConstruction.v. The implementation proves the signature
    law; it is not a new axiom. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import CardinalSuccessorUP AlephOneSquareConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Module Type AlephOneSquareSignature.
(** Source for [square_bound]: Federer 2.5.11, p. 102, the
    equation (card Y_1) times aleph-one equals aleph-one, in the
    injection form used by the cardinality estimate. *)
Parameter square_bound : forall (J : choiceType) (Y : set J),
  is_cardinal_successor (@setT nat) Y -> Y `*` Y #<= Y.
End AlephOneSquareSignature.

Module AlephOneSquare : AlephOneSquareSignature.
(** Source for [square_bound]: the proved transfinite construction
    discharges the signature law for Federer 2.5.11, p. 102. *)
Theorem square_bound (J : choiceType) (Y : set J) :
  is_cardinal_successor (@setT nat) Y -> Y `*` Y #<= Y.
Proof. exact: aleph_one_square_bound. Qed.
End AlephOneSquare.
