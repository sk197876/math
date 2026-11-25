(** Sealed infimum operator for Federer (1969), 2.9.1, p. 152. Only the
    greatest-lower-bound specification is exposed. Source context and
    construction: AbsoluteContinuousPartUP.v and
    AbsoluteContinuousPartConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AbsoluteContinuousPartSignature.
(** Source for [value]: abstract psi_phi of Federer 2.9.1, p. 152 *)
Parameter value : forall (R : realType) (X : topologicalType),
  (set X -> \bar R) -> (set X -> \bar R) -> set X -> \bar R.
(** Source for [laws]: infimum laws of Federer 2.9.1,
    p. 152. Existence is proved rather than assumed. *)
Parameter laws : forall (R : realType) (X : topologicalType) (phi psi : set X -> \bar R),
  is_absolutely_continuous_part phi psi (@value R X phi psi).
End AbsoluteContinuousPartSignature.
Module AbsoluteContinuousPart : AbsoluteContinuousPartSignature.
(** Source for [value]: opaque selection of the proved
    infimum operator in Federer 2.9.1, p. 152. *)
Definition value (R : realType) (X : topologicalType) (phi psi : set X -> \bar R) :=
  projT1 (cid (@continuous_part_exists R X phi psi)).
(** Source for [laws]: the selected operator has the
    proved order specification of Federer 2.9.1, p. 152. *)
Lemma laws (R : realType) (X : topologicalType) (phi psi : set X -> \bar R) :
  is_absolutely_continuous_part phi psi (@value R X phi psi).
Proof. exact: projT2 (cid (@continuous_part_exists R X phi psi)). Qed.
End AbsoluteContinuousPart.
