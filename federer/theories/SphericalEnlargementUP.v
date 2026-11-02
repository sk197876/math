(** Enlargement control for the spherical consequences in Federer (1969),
    2.10.19(3)–(5), p. 181. The radius-zero case will retain the original
    positive-radius ball as its own enlargement. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_enlargement_control]: supporting uniform control
    max(10,10^m) for 2.10.19, p. 181 The initial integer degree zero is
    included. *)
Definition spherical_enlargement_control (R : realType) (m : nat) : R :=
  Num.max 10 ((10 : R)^+m).

(** Source for [spherical_enlargement_control_ge_ten]: supporting diameter
    control for 2.10.19, p. 181 *)
Lemma spherical_enlargement_control_ge_ten (R : realType) m :
  10<=spherical_enlargement_control R m.
Proof. by rewrite /spherical_enlargement_control le_max lexx. Qed.

(** Source for [spherical_enlargement_control_ge_power]: supporting cost
    control for 2.10.19, p. 181 *)
Lemma spherical_enlargement_control_ge_power (R : realType) m :
  (10 : R)^+m<=spherical_enlargement_control R m.
Proof. by rewrite /spherical_enlargement_control le_max lexx orbT. Qed.

(** Source for [spherical_enlargement_control_positive]: supporting positive
    control constant in 2.10.19, p. 181 *)
Lemma spherical_enlargement_control_positive (R : realType) m :
  0<spherical_enlargement_control R m.
Proof.
have hp : (0<10 :> R) by rewrite ltr0n.
exact: lt_le_trans hp (spherical_enlargement_control_ge_ten R m).
Qed.
