(** Federer (1969), 4.1.25, p. 383: the
    scalar auxiliary quotient is opaque and exposes its
    independently specified original partial graph only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExteriorGrading AlternatingForms
  ExtendedRealOrderTopology PartialFunctionUP CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CurrentAreaPairingQuotientSignature.
(** Source for [value]: the actual auxiliary scalar
    quotient used in 4.1.25, p. 383. *)
Parameter value:forall (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m),
  partial_function (R_n R m) (extended_real_line R).
(** Source for [laws]: the exact original differential
    graph, including critical points, of 4.1.25, p. 383. *)
Parameter laws:forall (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m),
  is_current_area_pairing_quotient f xi a (@value R m n f xi a).
End CurrentAreaPairingQuotientSignature.

Module CurrentAreaPairingQuotient:CurrentAreaPairingQuotientSignature.
(** Source for [value]: select the already proved
    quotient witness for 4.1.25, p. 383. *)
Definition value (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) :
    partial_function (R_n R m) (extended_real_line R) :=
  projT1 (cid (@current_area_pairing_quotient_exists R m n f xi a)).
(** Source for [laws]: the hidden witness satisfies
    exactly the auxiliary graph of 4.1.25, p. 383. *)
Lemma laws (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) :
  is_current_area_pairing_quotient f xi a (@value R m n f xi a).
Proof.
exact:(projT2 (cid (@current_area_pairing_quotient_exists R m n f xi a))).
Qed.
End CurrentAreaPairingQuotient.
Arguments CurrentAreaPairingQuotient.value : clear implicits.
Arguments CurrentAreaPairingQuotient.laws : clear implicits.
