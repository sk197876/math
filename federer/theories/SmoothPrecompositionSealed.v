(** Federer (1969), 4.1.7, p. 359:
    the actual smooth precomposition is opaque.
    Its original value law is public;
    continuity must be proved from derivative
    bounds rather than added to this seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  SmoothFunctionSpaceUP SmoothPrecompositionUP SmoothPrecompositionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothPrecompositionSignature.
(** Source for [operator]: actual original
    smooth precomposition, supporting Federer
    4.1.7, p. 359. *)
Parameter operator:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z),
  is_smooth_function_space hNY hNZ B ev->is_smooth_function_space hNX hNZ A fv->
  forall f:X->Y,(forall x,A x->B (f x))->norm_class_all_orders hNX hNY A f->Hom E F.
(** Source for [laws]: the original
    pointwise precomposition law, supporting
    Federer 4.1.7, p. 359. *)
Parameter laws:forall (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z)
    (hE:is_smooth_function_space hNY hNZ B ev) (hF:is_smooth_function_space hNX hNZ A fv)
    (f:X->Y) (hImage:forall x,A x->B (f x)) (hf:norm_class_all_orders hNX hNY A f),
  is_smooth_precomposition A ev fv f
    (@operator R X Y Z NX NY NZ hNX hNY hNZ A B E F ev fv hE hF f hImage hf).
End SmoothPrecompositionSignature.
Module SmoothPrecomposition:SmoothPrecompositionSignature.
(** Source for [operator]: hide only the
    proved witness of precomposition, supporting
    Federer 4.1.7, p. 359. *)
Definition operator (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z)
    (hE:is_smooth_function_space hNY hNZ B ev) (hF:is_smooth_function_space hNX hNZ A fv)
    (f:X->Y) (hImage:forall x,A x->B (f x)) (hf:norm_class_all_orders hNX hNY A f):Hom E F:=
  projT1 (cid (@smooth_precomposition_exists R X Y Z NX NY NZ hNX hNY hNZ
    A B E F ev fv hE hF f hImage hf)).
(** Source for [laws]: the opaque operator
    satisfies its independent original value
    law, supporting Federer 4.1.7,
    p. 359. *)
Lemma laws (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z)
    (hE:is_smooth_function_space hNY hNZ B ev) (hF:is_smooth_function_space hNX hNZ A fv)
    (f:X->Y) (hImage:forall x,A x->B (f x)) (hf:norm_class_all_orders hNX hNY A f):
  is_smooth_precomposition A ev fv f
    (@operator R X Y Z NX NY NZ hNX hNY hNZ A B E F ev fv hE hF f hImage hf).
Proof.
exact:(projT2 (cid (@smooth_precomposition_exists R X Y Z NX NY NZ hNX hNY hNZ
  A B E F ev fv hE hF f hImage hf))).
Qed.
End SmoothPrecomposition.
