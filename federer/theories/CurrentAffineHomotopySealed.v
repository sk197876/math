(** Federer (1969), 4.1.13, pp. 369–370: the opaque
    affine homotopy exposes only the independently specified
    original formula. Consumers use its laws, not the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentAffineHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentAffineHomotopySignature.
(** Source for [value]: the original affine path joining
    f and g, Federer 4.1.13, p. 369. *)
Parameter value:forall (R:realType) (n nu:nat),
  (R_n R n->R_n R nu)->(R_n R n->R_n R nu)->
    R_n R (1+n)%N->R_n R nu.
(** Source for [laws]: the original formula
    (1-t)f(x)+tg(x), Federer 4.1.13, p. 369. *)
Parameter laws:forall (R:realType) (n nu:nat)
    (f g:R_n R n->R_n R nu),
  is_current_affine_homotopy f g (@value R n nu f g).
End CurrentAffineHomotopySignature.

Module CurrentAffineHomotopy:CurrentAffineHomotopySignature.
(** Source for [value]: seal the proved existence witness
    for Federer's original affine map, 4.1.13,
    pp. 369–370. *)
Definition value (R:realType) (n nu:nat)
    (f g:R_n R n->R_n R nu):R_n R (1+n)%N->R_n R nu:=
  projT1 (cid (@current_affine_homotopy_exists R n nu f g)).
(** Source for [laws]: the sealed witness satisfies
    the independently specified formula of Federer
    4.1.13, p. 369. *)
Lemma laws (R:realType) (n nu:nat)
    (f g:R_n R n->R_n R nu):
  is_current_affine_homotopy f g (@value R n nu f g).
Proof. exact:(projT2 (cid (@current_affine_homotopy_exists R n nu f g))). Qed.
End CurrentAffineHomotopy.
