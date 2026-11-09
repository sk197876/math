(** Federer (1969), 3.3.20, p. 306:
    opaque original fixed-binary Cantor factor. *)
From mathcomp Require Import all_boot all_algebra reals boolp classical_sets.
From Federer Require Import RealMetricBackground BinaryCantorSetUP BinaryCantorSetExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type BinaryPowerCantorSignature.
(** Source for [value]: the actual original fixed-binary
    A(m,n) in 3.3.20, p. 306, 0<m<1. *)
Parameter value:forall (R:realType) (m:R),0<m ->m<1 ->set (real_line_metric R).
(** Source for [laws]: independent original factor laws,
    3.3.20, p. 306; geometric conclusions are derived. *)
Parameter laws:forall R m hm hm1,is_binary_power_cantor_set m (@value R m hm hm1).
End BinaryPowerCantorSignature.
Module BinaryPowerCantor:BinaryPowerCantorSignature.
(** Source for [value]: hidden local existence witness
    for the original factor, 3.3.20, p. 306. *)
Definition value (R:realType) (m:R) (hm:0<m) (hm1:m<1):=
  projT1 (cid (@binary_power_cantor_set_exists R m hm hm1)).
(** Source for [laws]: the hidden witness satisfies
    the independent original laws, 3.3.20, p. 306. *)
Lemma laws R m hm hm1:is_binary_power_cantor_set m (@value R m hm hm1).
Proof. exact:(projT2 (cid (@binary_power_cantor_set_exists R m hm hm1))). Qed.
End BinaryPowerCantor.
