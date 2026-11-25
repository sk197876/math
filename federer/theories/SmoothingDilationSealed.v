(** Federer (1969), 4.1.2, p. 346: opaque
    family of the specified positive-scale kernel dilations.
    The formula implementation is used only for existence. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations SmoothingDilationUP SmoothingDilationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothingDilationSignature.
(** Source for [value]: the original Phi_epsilon
    family, Federer 4.1.2, p. 346. *)
Parameter value:forall (R:realType) n,(R_n R n->R)->R->R_n R n->R.
(** Source for [laws]: the exact positive-scale
    dilation equation, Federer 4.1.2, p. 346. *)
Parameter laws:forall (R:realType) n (phi:R_n R n->R),
  @is_smoothing_dilation R n phi (@value R n phi).
End SmoothingDilationSignature.
Module SmoothingDilation:SmoothingDilationSignature.
(** Source for [value]: select the already proved
    dilation family, Federer 4.1.2, p. 346. *)
Definition value (R:realType) n (phi:R_n R n->R):R->R_n R n->R:=
  projT1 (cid (@smoothing_dilation_exists R n phi)).
(** Source for [laws]: the hidden family has
    exactly the prescribed values, Federer 4.1.2, p. 346. *)
Lemma laws (R:realType) n (phi:R_n R n->R):
  @is_smoothing_dilation R n phi (@value R n phi).
Proof. exact:(projT2 (cid (@smoothing_dilation_exists R n phi))). Qed.
End SmoothingDilation.
