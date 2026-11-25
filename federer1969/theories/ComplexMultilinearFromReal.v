(** Federer (1969), 3.4.12, p. 338:
    actual real multilinearity and the additional complex
    scalar laws imply full complex multilinearity. Reuse
    real additivity in each slot; introduce no new
    multilinear-map carrier or algebraic assumption. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed TensorFamilyUP FamilyUpdate
  ComplexScalarSlotUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_multilinear_from_real]: the exact
    complex m-linearity conclusion for actual higher jets
    in 3.4.12, p. 338. This supporting
    algebraic connection also includes the empty argument family. *)
Theorem complex_multilinear_from_real (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) k (F:{ffun 'I_k->X}->Y):
  @multilinear R k (fun _=>restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) F ->
  has_complex_scalar_slot_laws F ->
  @multilinear (ComplexScalars.C R) k (fun _=>X) Y F.
Proof.
move=>hReal hScalar u i c x y.
have hAdd:=hReal u i (1:R) (c*:x) y.
rewrite !scale1r in hAdd.
by rewrite hAdd hScalar.
Qed.
