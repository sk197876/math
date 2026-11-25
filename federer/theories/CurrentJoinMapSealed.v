(** Federer (1969), 4.1.11, p. 364: the original map F for
    the join of currents. Its opaque interface exposes only the
    independently specified formula F(x,t,y)=(1-t)x+ty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentJoinMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentJoinMapSignature.
(** Source for [value]: the original join map F,
    Federer 4.1.11, p. 364, opening display. *)
Parameter value : forall (R : realType) (n : nat),
  R_n R (n+(1+n))%N -> R_n R n.
(** Source for [laws]: the original affine formula determines F,
    Federer 4.1.11, p. 364. *)
Parameter laws : forall (R : realType) (n : nat),
  @is_current_join_map R n (@value R n).
End CurrentJoinMapSignature.

Module CurrentJoinMap : CurrentJoinMapSignature.
(** Source for [value]: seal an existence witness for F,
    supporting Federer 4.1.11, p. 364. *)
Definition value (R : realType) (n : nat) :
    R_n R (n+(1+n))%N -> R_n R n :=
  projT1 (cid (@current_join_map_exists R n)).
(** Source for [laws]: the sealed map satisfies the original
    affine formula, supporting Federer 4.1.11, p. 364. *)
Lemma laws (R : realType) (n : nat) :
  @is_current_join_map R n (@value R n).
Proof. exact: (projT2 (cid (@current_join_map_exists R n))). Qed.
End CurrentJoinMap.
