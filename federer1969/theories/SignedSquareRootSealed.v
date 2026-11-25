(** Opaque auxiliary scalar square root for Federer
    (1969), 3.2.7, p. 246. Only its proved
    half-line laws are exposed. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import SignedSquareRootUP SignedSquareRootConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SignedSquareRootSignature.
(** Source for [value]: auxiliary signed square root
    supporting the third example of Federer 3.2.7, p. 246. *)
Parameter value:forall R:realType,R->R.
(** Source for [laws]: independently specified scalar laws
    supporting the third example of Federer 3.2.7, p. 246. *)
Parameter laws:forall R:realType,is_signed_square_root (@value R).
End SignedSquareRootSignature.
Module SignedSquareRoot:SignedSquareRootSignature.
(** Source for [value]: hidden witness selected from proved
    existence for Federer 3.2.7, p. 246. *)
Definition value (R:realType):=projT1 (cid (@signed_square_root_exists R)).
(** Source for [laws]: proof that the selected witness
    obeys the defining laws supporting Federer 3.2.7, p. 246. *)
Lemma laws (R:realType):is_signed_square_root (@value R).
Proof. exact (projT2 (cid (@signed_square_root_exists R))). Qed.
End SignedSquareRoot.
