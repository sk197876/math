(** Federer (1969), 3.4.12, p. 338:
    the additional complex scalar law of an actual
    real multilinear evaluation. Additivity already belongs to
    the original real multilinear-space interface; this predicate
    specifies only the missing complex scalar compatibility. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed FamilyUpdate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [has_complex_scalar_slot_laws]: complex
    linearity in each original higher derivative argument,
    as asserted in 3.4.12, p. 338.
    This independent predicate assumes no derivative existence
    and no theorem about holomorphic functions. *)
Definition has_complex_scalar_slot_laws (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) k (F:{ffun 'I_k->X}->Y):Prop:=
  forall u (i:'I_k) c x,F (@family_with k (fun _=>X) u i (c*:x))=
    c*:F (@family_with k (fun _=>X) u i x).
