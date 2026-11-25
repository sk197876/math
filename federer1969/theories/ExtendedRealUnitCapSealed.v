(** Opaque scalar cap supporting the finite metric carrier
    for Federer (1969), 3.2.46, p. 281. The original
    path infimum remains a separate, already sealed object. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import ExtendedRealUnitCapUP ExtendedRealUnitCapConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ExtendedRealUnitCapSignature.
(** Source for [value]: technical finite scalar cap for
    3.2.46, p. 281, specified by its independent laws. *)
Parameter value : forall R : realType, \bar R -> R.
(** Source for [laws]: the finite-input and infinity cap
    laws supporting 3.2.46, p. 281. *)
Parameter laws : forall R : realType, is_extended_real_unit_cap (@value R).
End ExtendedRealUnitCapSignature.

Module ExtendedRealUnitCap : ExtendedRealUnitCapSignature.
(** Source for [value]: private choice of the proved cap
    witness supporting 3.2.46, p. 281. *)
Definition value (R : realType) := projT1 (cid (@extended_real_unit_cap_exists R)).
(** Source for [laws]: the chosen witness satisfies all
    independently stated cap laws for 3.2.46, p. 281. *)
Lemma laws (R : realType) : is_extended_real_unit_cap (@value R).
Proof. exact: projT2 (cid (@extended_real_unit_cap_exists R)). Qed.
End ExtendedRealUnitCap.
