(** Opaque finite uniform norm supporting the
    derivative suprema in Federer (1969), 3.1.13,
    p. 225. Only the existing
    least-bound laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import UniformFunctionNormUP BoundedFunctionNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type BoundedFunctionNormSignature.
(** Source for [value]: the finite supremum
    used for G_i, Federer 3.1.13, p. 225. *)
Parameter value : forall (R : realType) (X : Type) (f : X->R),
  (exists C : R, 0<=C /\ forall x, `|f x|<=C) -> R.
(** Source for [laws]: the finite supremum
    satisfies the least-bound specification, Federer
    3.1.13, p. 225. *)
Parameter laws : forall (R : realType) (X : Type) (f : X->R)
  (hb : exists C : R, 0<=C /\ forall x, `|f x|<=C),
  is_uniform_function_norm f (@value R X f hb).
End BoundedFunctionNormSignature.

Module BoundedFunctionNorm : BoundedFunctionNormSignature.
(** Source for [value]: selection from the
    privately proved supremum existence theorem,
    Federer 3.1.13, p. 225. *)
Definition value (R : realType) (X : Type) (f : X->R)
    (hb : exists C : R, 0<=C /\ forall x, `|f x|<=C) : R :=
  projT1 (cid (@bounded_function_norm_exists R X f hb)).
(** Source for [laws]: proof of the
    public least-bound laws, Federer 3.1.13, p. 225. *)
Lemma laws (R : realType) (X : Type) (f : X->R)
    (hb : exists C : R, 0<=C /\ forall x, `|f x|<=C) :
  is_uniform_function_norm f (@value R X f hb).
Proof. exact: (projT2 (cid (@bounded_function_norm_exists R X f hb))). Qed.
End BoundedFunctionNorm.
