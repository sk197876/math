(** Federer (1969), 4.1.2, p. 346: opaque
    choice of the already proved smoothing kernel. Only
    its independently specified original laws are public. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations SmoothingKernelUP SmoothingKernelExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothingKernelSignature.
(** Source for [value]: an original smooth nonnegative
    unit-integral kernel, Federer 4.1.2, p. 346. *)
Parameter value:forall (R:realType) n,R_n R n->R.
(** Source for [laws]: actual support, nonnegativity,
    smoothness and normalization, Federer 4.1.2, p. 346. *)
Parameter laws:forall (R:realType) n,@is_smoothing_kernel R n (@value R n).
End SmoothingKernelSignature.
Module SmoothingKernel:SmoothingKernelSignature.
(** Source for [value]: select the proved witness
    behind the interface, Federer 4.1.2, p. 346. *)
Definition value (R:realType) n:R_n R n->R:=projT1 (cid (@smoothing_kernel_exists R n)).
(** Source for [laws]: the hidden witness has
    every original kernel law, Federer 4.1.2, p. 346. *)
Lemma laws (R:realType) n:@is_smoothing_kernel R n (@value R n).
Proof. exact:(projT2 (cid (@smoothing_kernel_exists R n))). Qed.
End SmoothingKernel.
