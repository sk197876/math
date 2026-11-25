(** Federer (1969), 4.1.25, p. 383: opaque
    auxiliary scalar quotient for the actual variable
    target form, exposing only its independent graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExteriorGrading AlternatingForms
  ExtendedRealOrderTopology PartialFunctionUP CurrentAreaPairingQuotientTestUP
  CurrentAreaPairingQuotientTestExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CurrentAreaPairingQuotientTestSignature.
(** Source for [value]: the variable-form area
    auxiliary of 4.1.25, p. 383. *)
Parameter value:forall (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m),
  partial_function (R_n R m) (extended_real_line R).
(** Source for [laws]: the exact original differential
    graph of the auxiliary in 4.1.25, p. 383. *)
Parameter laws:forall (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m),
  is_current_area_pairing_quotient_test f xi phi (@value R m n f xi phi).
End CurrentAreaPairingQuotientTestSignature.

Module CurrentAreaPairingQuotientTest:CurrentAreaPairingQuotientTestSignature.
(** Source for [value]: choose the proved witness
    for the auxiliary of 4.1.25, p. 383. *)
Definition value (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m) :
    partial_function (R_n R m) (extended_real_line R) :=
  projT1 (cid (@current_area_pairing_quotient_test_exists R m n f xi phi)).
(** Source for [laws]: the selected witness satisfies
    the independently stated graph of 4.1.25, p. 383. *)
Lemma laws (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m) :
  is_current_area_pairing_quotient_test f xi phi (@value R m n f xi phi).
Proof.
exact:(projT2 (cid (@current_area_pairing_quotient_test_exists R m n f xi phi))).
Qed.
End CurrentAreaPairingQuotientTest.
Arguments CurrentAreaPairingQuotientTest.value : clear implicits.
Arguments CurrentAreaPairingQuotientTest.laws : clear implicits.
