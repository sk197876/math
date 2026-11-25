(** Federer (1969), 4.1.10, p. 364: the original affine
    contraction from the constant map u to the identity. The opaque
    map exposes only its independently specified affine formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentConeHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentConeHomotopySignature.
(** Source for [value]: the original affine contraction in
    Federer 4.1.10, p. 364, opening sentence. *)
Parameter value : forall (R : realType) (n : nat),
  R_n R n -> R_n R (1+n)%N -> R_n R n.
(** Source for [laws]: at time t, x is sent to (1-t)u+tx,
    Federer 4.1.10, p. 364. *)
Parameter laws : forall (R : realType) (n : nat) (u : R_n R n),
  is_current_cone_homotopy u (@value R n u).
End CurrentConeHomotopySignature.

Module CurrentConeHomotopy : CurrentConeHomotopySignature.
(** Source for [value]: seal the existence witness for the
    original affine formula, supporting Federer 4.1.10, p. 364. *)
Definition value (R : realType) (n : nat) (u : R_n R n) :
    R_n R (1+n)%N -> R_n R n :=
  projT1 (cid (@current_cone_homotopy_exists R n u)).
(** Source for [laws]: the sealed map satisfies the original
    affine formula, supporting Federer 4.1.10, p. 364. *)
Lemma laws (R : realType) (n : nat) (u : R_n R n) :
  is_current_cone_homotopy u (@value R n u).
Proof. exact: (projT2 (cid (@current_cone_homotopy_exists R n u))). Qed.
End CurrentConeHomotopy.
