(** Opaque level counts and radii for Federer (1969),
    3.3.19, p. 302. Only proved recurrence laws cross the seal. *)
From mathcomp Require Import all_boot reals boolp.
From Federer Require Import FactorialDiscScalesUP FactorialDiscScalesConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FactorialDiscScalesSignature.
(** Source for [count]: original level counts in 3.3.19,
    p. 302; index j denotes book level j+3. *)
Parameter count:forall R:realType,nat->nat.
(** Source for [radius]: original radii in 3.3.19,
    p. 302; the auxiliary level zero is the unit root. *)
Parameter radius:forall R:realType,nat->R.
(** Source for [laws]: independent proved initial and
    subdivision laws from 3.3.19, p. 302. *)
Parameter laws:forall R:realType,is_factorial_disc_scales (@count R) (@radius R).
End FactorialDiscScalesSignature.
Module FactorialDiscScales:FactorialDiscScalesSignature.
(** Source for [count]: local recursive existence witness
    hidden behind the 3.3.19, p. 302 specification. *)
Definition count (R:realType):=projT1 (cid (factorial_disc_scales_exists R)).
(** Source for [radius]: local radius witness hidden behind
    the 3.3.19, p. 302 specification. *)
Definition radius (R:realType):=projT1 (cid (projT2 (cid (factorial_disc_scales_exists R)))).
(** Source for [laws]: the selected witnesses satisfy the
    3.3.19, p. 302 recurrence specification. *)
Lemma laws (R:realType):is_factorial_disc_scales (@count R) (@radius R).
Proof. exact:(projT2 (cid (projT2 (cid (factorial_disc_scales_exists R))))). Qed.
End FactorialDiscScales.
