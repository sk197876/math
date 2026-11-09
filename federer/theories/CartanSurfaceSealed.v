(** Federer (1969), 3.4.5, p. 321: the actual
    surface is opaque, with only its independent original
    cubic membership specification exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations CartanSurfaceUP CartanSurfaceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CartanSurfaceSignature.
(** Source for [set]: the cubic surface for the
    local/global distinction cited in 3.4.5, p. 321. *)
Parameter set:forall R:realType,set (R_n R 3).
(** Source for [laws]: actual membership, with no
    counterexample conclusion assumed, 3.4.5, p. 321. *)
Parameter laws:forall R:realType,is_cartan_flat_surface (@set R).
End CartanSurfaceSignature.
Module CartanSurface:CartanSurfaceSignature.
(** Source for [set]: a private proved membership-law
    witness, supporting 3.4.5, p. 321. *)
Definition set (R:realType):set (R_n R 3):=
  projT1 (cid (@cartan_flat_surface_exists R)).
(** Source for [laws]: the selected set satisfies the
    independent equation, supporting 3.4.5, p. 321. *)
Lemma laws (R:realType):is_cartan_flat_surface (@set R).
Proof. exact:(projT2 (cid (@cartan_flat_surface_exists R))). Qed.
End CartanSurface.
