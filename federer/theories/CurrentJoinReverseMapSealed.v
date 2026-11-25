(** Federer (1969), 4.1.11, p. 365: the original map p for
    the join of currents. Its opaque interface exposes only the
    independently specified formula p(x,t,y)=(y,1-t,x). *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentJoinReverseMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentJoinReverseMapSignature.
(** Source for [value]: the original reversing map p,
    Federer 4.1.11, p. 365, opening display. *)
Parameter value : forall (R : realType) (n : nat),
  R_n R (n+(1+n))%N -> R_n R (n+(1+n))%N.
(** Source for [laws]: the original coordinate formula determines p,
    Federer 4.1.11, p. 365. *)
Parameter laws : forall (R : realType) (n : nat),
  @is_current_join_reverse_map R n (@value R n).
End CurrentJoinReverseMapSignature.

Module CurrentJoinReverseMap : CurrentJoinReverseMapSignature.
(** Source for [value]: seal an existence witness for p,
    supporting Federer 4.1.11, p. 365. *)
Definition value (R : realType) (n : nat) :
    R_n R (n+(1+n))%N -> R_n R (n+(1+n))%N :=
  projT1 (cid (@current_join_reverse_map_exists R n)).
(** Source for [laws]: the sealed map satisfies the original
    affine formula, supporting Federer 4.1.11, p. 365. *)
Lemma laws (R : realType) (n : nat) :
  @is_current_join_reverse_map R n (@value R n).
Proof. exact: (projT2 (cid (@current_join_reverse_map_exists R n))). Qed.
End CurrentJoinReverseMap.
