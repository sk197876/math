(** Opaque pointwise supremum of set functions, supporting
    Federer (1969), 3.3.4, p. 291. Its construction
    is private; all downstream arguments use the order laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureFamilySupremumUP MeasureFamilySupremumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type MeasureFamilySupremumSignature.
(** Source for [value]: the actual pointwise supremum
    in the measures psi_v, Federer 3.3.4, p. 291. *)
Parameter value:forall (R:realType) (X J:Type),
  set J->(J->set X->\bar R)->set X->\bar R.
(** Source for [laws]: the previously specified order
    laws for the supremum in Federer 3.3.4, p. 291. *)
Parameter laws:forall (R:realType) (X J:Type) D nu,
  is_measure_family_supremum D nu (@value R X J D nu).
End MeasureFamilySupremumSignature.

Module MeasureFamilySupremum:MeasureFamilySupremumSignature.
(** Source for [value]: a private witness of proved
    existence for the supremum in Federer 3.3.4, p. 291. *)
Definition value (R:realType) (X J:Type) (D:set J) (nu:J->set X->\bar R):=
  projT1 (cid (measure_family_supremum_exists D nu)).
(** Source for [laws]: this witness satisfies the
    independent order specification, Federer 3.3.4, p. 291. *)
Lemma laws (R:realType) (X J:Type) D nu:
  is_measure_family_supremum D nu (@value R X J D nu).
Proof. exact:projT2 (cid (measure_family_supremum_exists D nu)). Qed.
End MeasureFamilySupremum.
