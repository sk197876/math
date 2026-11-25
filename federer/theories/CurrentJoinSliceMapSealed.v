(** Federer (1969), 4.1.11, p. 365: the original
    insertion G_t(x,y)=(x,t,y). Its opaque interface exposes only
    the independent coordinate formula, after proved existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentJoinSliceMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CurrentJoinSliceMapSignature.
(** Source for [value]: the original G_t, Federer 4.1.11,
    p. 365, opening paragraph. *)
Parameter value : forall (R : realType) (n : nat) (t : R),
  R_n R (n+n)%N -> R_n R (n+(1+n))%N.
(** Source for [laws]: G_t has exactly the original
    coordinates, Federer 4.1.11, p. 365. *)
Parameter laws : forall (R : realType) (n : nat) (t : R),
  @is_current_join_slice_map R n t (@value R n t).
End CurrentJoinSliceMapSignature.

Module CurrentJoinSliceMap : CurrentJoinSliceMapSignature.
(** Source for [value]: hide the proved insertion witness,
    supporting Federer 4.1.11, p. 365. *)
Definition value (R : realType) (n : nat) (t : R) :
    R_n R (n+n)%N -> R_n R (n+(1+n))%N :=
  projT1 (cid (@current_join_slice_map_exists R n t)).
(** Source for [laws]: the opaque insertion has its
    independently specified coordinates, supporting Federer
    4.1.11, p. 365. *)
Lemma laws (R : realType) (n : nat) (t : R) :
  @is_current_join_slice_map R n t (@value R n t).
Proof. exact: (projT2 (cid (@current_join_slice_map_exists R n t))). Qed.
End CurrentJoinSliceMap.
