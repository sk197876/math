(** Federer (1969), 4.1.7, pp. 355–356: the
    coefficient-linear smooth operators used in the
    original current operations. The pointwise law
    specifies each operator independently. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_target_operator]: the original
    pointwise coefficient action, supporting the current
    operations in Federer 4.1.7, pp. 355–356. *)
Definition is_smooth_target_operator (R:realType) (X Y Z:lmodType R)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (L:Hom Y Z) (P:Hom E F):=
  forall f x,U x->fv (P f) x=L (ev f x).

(** Source for [smooth_target_operator_unique]: original
    smooth fields are determined by their values, so
    this coefficient operator is unique; supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma smooth_target_operator_unique (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (U:X->Prop) (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (hF:is_smooth_function_space hNX hNZ U fv) (L:Hom Y Z) (P Q:Hom E F):
  is_smooth_target_operator U ev fv L P ->
  is_smooth_target_operator U ev fv L Q ->P=Q.
Proof.
move=>hP hQ; apply:hom_ext=>f; apply:(smooth_function_extensional hF)=>x hx.
by rewrite (@hP f x hx) (@hQ f x hx).
Qed.
