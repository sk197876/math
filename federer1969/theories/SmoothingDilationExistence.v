(** Federer (1969), 4.1.2, p. 346: existence
    of the specified kernel dilation. The formula is
    used only to prove existence; consumers use the
    independently stated positive-scale law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smoothing_dilation_exists]: an actual family
    satisfies the original rescaling definition,
    Federer 4.1.2, p. 346. *)
Theorem smoothing_dilation_exists (R:realType) n (phi:R_n R n->R):
  exists family,is_smoothing_dilation phi family.
Proof. exists (fun e x=>(e^+n)^-1*phi (e^-1*:x)); by move=>e he x. Qed.
