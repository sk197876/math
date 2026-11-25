(** Federer (1969), 3.4.12, p. 339:
    the original complex coefficient field has characteristic
    zero. Transfer the existing real characteristic through
    the original injective field embedding, as in 1.6.6,
    pp. 26–27. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_characteristic_zero]: every
    factorial normalization in the original complex forms
    is valid, 3.4.12, p. 339. The
    scalar field remains opaque. *)
Theorem complex_scalar_characteristic_zero (R:realFieldType):
  [pchar (ComplexScalars.C R)] =i pred0.
Proof.
move=>p;rewrite (fmorph_pchar (ComplexScalars.embed R) p);exact:pchar_num.
Qed.
