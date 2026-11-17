(** Federer (1969), 3.4.10, p. 338:
    the cited surface is opaque after
    proved existence. Its public interface states
    only the original polynomial equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations BruhatWhitneySurfaceUP BruhatWhitneySurfaceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type BruhatWhitneySurfaceSignature.
(** Source for [set]: the original surface
    cited in 3.4.10, p. 338. *)
Parameter set:forall R:realType,set (R_n R 3).
(** Source for [laws]: only the equation
    in Bruhat and Whitney, section 11(c),
    p. 159, is exposed. *)
Parameter laws:forall R:realType,is_bruhat_whitney_surface (@set R).
End BruhatWhitneySurfaceSignature.
Module BruhatWhitneySurface:BruhatWhitneySurfaceSignature.
(** Source for [set]: a private selected
    witness after proved existence, supporting
    the cited example in 3.4.10, p. 338. *)
Definition set (R:realType):set (R_n R 3):=
  projT1 (cid (@bruhat_whitney_surface_exists R)).
(** Source for [laws]: the selected witness
    satisfies the independent original equation,
    supporting 3.4.10, p. 338. *)
Lemma laws (R:realType):is_bruhat_whitney_surface (@set R).
Proof. exact:(projT2 (cid (@bruhat_whitney_surface_exists R))). Qed.
End BruhatWhitneySurface.
