(** Federer (1969), 3.2.33, p. 270: the actual
    analytic coordinate differential satisfies the class-one
    field laws needed by 3.1.18, pp. 229–230. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_one_actual_field]: any actual
    first derivative field of a class-one map has the
    printed class-one continuity laws, supporting the use
    of 3.1.18 in Federer 3.2.33, p. 270.
    Ordinary differential uniqueness transfers the laws;
    no continuity premise is added for the given field. *)
Lemma norm_class_one_actual_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) (D:X->Hom X Y):
  norm_class_one NX NY A f ->
  (forall x,A x ->has_norm_differential NX NY A f x (D x)) ->
  is_norm_class_one_field NX NY A f D.
Proof.
move=>[E hE] hD.
have hEqual x (hx:A x):D x=E x.
  exact:(norm_differential_unique hNX hNY (hD x hx) (norm_class_one_differential hE hx)).
constructor.
- exact:norm_class_one_zero hE.
- exact hD.
- move=>a ha e he; have [r [hr hb]]:=norm_class_one_continuity hE ha he.
  exists r; split=>// h hh hSmall v.
  rewrite (@hEqual (a+h) hh) (@hEqual a ha).
  exact:hb h hh hSmall v.
Qed.
