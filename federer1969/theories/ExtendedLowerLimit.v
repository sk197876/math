(** Public scalar lower limit supporting Federer (1969), 2.4.6, p. 84,
    exposing only the sealed order specification. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedLowerLimitUP ExtendedLowerLimitSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit]: the scalar lower limit
    of integral values in Federer 2.4.6, p. 84. *)
Definition extended_lower_limit (R : realType) (u : nat -> \bar R) :=
  ExtendedLowerLimit.value u.

(** Source for [extended_lower_limit_laws]: public supremum
    specification for the lower limit in Federer 2.4.6, p. 84. *)
Lemma extended_lower_limit_laws (R : realType) (u : nat -> \bar R) :
  is_extended_lower_limit u (extended_lower_limit u).
Proof. exact: ExtendedLowerLimit.laws. Qed.

(** Source for [extended_lower_limit_constant]: supporting
    constant-sequence boundary case for the lower limit in
    Federer 2.4.6, p. 84, including either infinity. *)
Lemma extended_lower_limit_constant (R : realType) (a : \bar R) :
  extended_lower_limit (fun _ : nat => a) = a.
Proof.
apply: (@extended_lower_limit_unique R (fun _ : nat => a) _ a (extended_lower_limit_laws _)).
constructor.
- move=> b [N hN]; exact: hN N (leqnn N).
- move=> b hb; apply: hb; exists 0%N=> n _; exact: lexx.
Qed.
