(** Federer (1969), 4.1.7, p. 359:
    precomposition on the actual spaces of
    smooth functions supports the original
    form pullback and proper current pushforward.
    Its value law is independent of
    every construction or continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_precomposition]: the
    original smooth precomposition h to h
    composed with f, supporting the pullback
    in Federer 4.1.7, p. 359. *)
Definition is_smooth_precomposition (R:realType) (X Y Z:lmodType R)
    (A:X->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z)
    (f:X->Y) (P:Hom E F):Prop:=
  forall h x,A x->fv (P h) x=ev h (f x).

(** Source for [smooth_precomposition_unique]: the
    original smooth precomposition is unique
    by its values on the open
    domain, supporting Federer 4.1.7,
    p. 359. *)
Lemma smooth_precomposition_unique (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (A:X->Prop) (E F:lmodType R) (ev:E->Y->Z) (fv:F->X->Z)
    (hF:is_smooth_function_space hNX hNZ A fv) (f:X->Y) (P Q:Hom E F):
  is_smooth_precomposition A ev fv f P->is_smooth_precomposition A ev fv f Q->P=Q.
Proof.
move=>hP hQ;apply:hom_ext=>h;apply:(smooth_function_extensional hF)=>x hx.
by rewrite (@hP h x hx) (@hQ h x hx).
Qed.
