(** Federer (1969), 3.4.1, p. 310: opaque actual rank-threshold source and image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations CriticalValueLociUP CriticalValueLociExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CriticalValuesSignature.
(** Source for [locus]: the original rank-threshold source of
    3.4.1, p. 310. The normed target may be infinite dimensional. *)
Parameter locus:forall (R:realType) m (Y:lmodType R),
  (Y->R)->set (R_n R m)->(R_n R m->Y)->nat->set (R_n R m).
(** Source for [image]: the original image from 3.4.1, p. 310.
    This field carries no nullity, measurability or finite-mass assertion. *)
Parameter image:forall (R:realType) m (Y:lmodType R),
  (Y->R)->set (R_n R m)->(R_n R m->Y)->nat->set Y.
(** Source for [laws]: independent original set laws from 3.4.1,
    p. 310, before any theorem about their Hausdorff measure is proved. *)
Parameter laws:forall (R:realType) m (Y:lmodType R) NY A f nu,
  is_critical_value_loci NY A f nu (@locus R m Y NY A f nu) (@image R m Y NY A f nu).
End CriticalValuesSignature.
Module CriticalValues:CriticalValuesSignature.
(** Source for [locus]: the private source witness for 3.4.1,
    p. 310, hidden by the opaque signature. *)
Definition locus (R:realType) m (Y:lmodType R) NY A f nu:=
  projT1 (cid (@critical_value_loci_exists R m Y NY A f nu)).
(** Source for [image]: the private image witness for 3.4.1,
    p. 310, hidden by the opaque signature. *)
Definition image (R:realType) m (Y:lmodType R) NY A f nu:=
  projT1 (cid (projT2 (cid (@critical_value_loci_exists R m Y NY A f nu)))).
(** Source for [laws]: both private witnesses satisfy exactly the
    independent set laws of 3.4.1, p. 310. *)
Lemma laws (R:realType) m (Y:lmodType R) NY A f nu:
  is_critical_value_loci NY A f nu (@locus R m Y NY A f nu) (@image R m Y NY A f nu).
Proof. exact:(projT2 (cid (projT2 (cid (@critical_value_loci_exists R m Y NY A f nu))))). Qed.
End CriticalValues.
