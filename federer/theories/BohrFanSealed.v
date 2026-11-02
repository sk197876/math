(** Sealed finite-fan witnesses supporting Federer (1969),
    2.8.20, p. 152; Saks1934 Lemma B, p. 258,
    and Cesari1939 Lemma III, p. 306. The coordinate
    construction is private, and all downstream arguments use
    BohrFanUP.v alone. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals.
From Federer Require Import BohrFanUP BohrFanConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type BohrFanSignature.
(** Source for [value]: abstract fan and core pair supporting
    Federer 2.8.20, p. 152; BohrFanUP.v. *)
Parameter value : forall (R : realType) (r : nat), (0 < r)%N ->
  ('I_r -> set (R*R)) * set (R*R).
(** Source for [laws]: the selected fan satisfies the proved
    specification supporting Federer 2.8.20, p. 152. *)
Parameter laws : forall (R : realType) (r : nat) (hr : (0 < r)%N),
  is_bohr_fan (@value R r hr).1 (@value R r hr).2.
End BohrFanSignature.
Module BohrFan : BohrFanSignature.
(** Source for [value]: opaque selection from the existence
    proof supporting Federer 2.8.20, p. 152. *)
Definition value (R : realType) r (hr : (0 < r)%N) :=
  projT1 (cid (@bohr_fan_pair_exists R r hr)).
(** Source for [laws]: the existence proof certifies the
    selected fan supporting Federer 2.8.20, p. 152. *)
Lemma laws (R : realType) r (hr : (0 < r)%N) :
  is_bohr_fan (@value R r hr).1 (@value R r hr).2.
Proof. exact: projT2 (cid (@bohr_fan_pair_exists R r hr)). Qed.
End BohrFan.
