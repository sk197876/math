(** Sealed local finite groups supporting Federer (1969),
    2.8.20, p. 152. Only the abstract patch laws
    are exposed. The coordinate construction and strip argument
    remain private; see BohrPatchConstruction.v for the source
    comparison with Saks1934 and Cesari1939. *)
From mathcomp Require Import all_boot boolp classical_sets reals.
From Federer Require Import ScalarHalfOpenRectangles BohrPatchUP BohrPatchConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type BohrPatchSignature.
(** Source for [value]: abstract patch data supporting
    Federer 2.8.20, p. 152. *)
Parameter value : forall (R : realType) r (Q : set (R*R)),
  (0<r)%N -> is_nondegenerate_half_open_rectangle Q ->
  (('I_r -> set (R*R))*('I_r -> set (R*R)))*set (R*R).
(** Source for [laws]: the proved abstract patch specification
    supporting Federer 2.8.20, p. 152. *)
Parameter laws : forall (R : realType) r (Q : set (R*R))
  (hr : (0<r)%N) (hQ : is_nondegenerate_half_open_rectangle Q),
  is_bohr_patch Q (@value R r Q hr hQ).1.1 (@value R r Q hr hQ).1.2 (@value R r Q hr hQ).2.
End BohrPatchSignature.
Module BohrPatch : BohrPatchSignature.
(** Source for [value]: opaque witness selection supporting
    Federer 2.8.20, p. 152, from the proved
    local-group existence theorem. *)
Definition value (R : realType) r (Q : set (R*R))
    (hr : (0<r)%N) (hQ : is_nondegenerate_half_open_rectangle Q) :=
  projT1 (cid (@bohr_patch_data_exists R r Q hr hQ)).
(** Source for [laws]: the selected patch has the proved
    laws supporting Federer 2.8.20, p. 152. *)
Lemma laws (R : realType) r (Q : set (R*R))
    (hr : (0<r)%N) (hQ : is_nondegenerate_half_open_rectangle Q) :
  is_bohr_patch Q (@value R r Q hr hQ).1.1 (@value R r Q hr hQ).1.2 (@value R r Q hr hQ).2.
Proof. exact: projT2 (cid (@bohr_patch_data_exists R r Q hr hQ)). Qed.
End BohrPatch.
