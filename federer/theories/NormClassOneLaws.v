(** Supporting consequences of the class-zero and class-one
    definitions in Federer (1969), 3.1.1, p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormDifferentialDirectional NormClassOneUP
  NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_everywhere_differentiable_class_zero]: the
    class-zero condition in Federer 3.1.1, p. 210, follows already from
    differentiability at every domain point. Interior is part of the
    definition on p. 209, so openness needs no added hypothesis. *)
Lemma norm_everywhere_differentiable_class_zero (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (D : X -> Hom X Y) :
  (forall a, A a -> has_norm_differential NX NY A f a (D a)) ->
  norm_class_zero NX NY A f.
Proof.
move=> hf a ha; split.
- exact: norm_differential_interior (hf a ha).
- move=> e he; exact: (norm_differential_continuous_at hNY (hf a ha) he).
Qed.

(** Source for [norm_class_one_field_unique]: Df in the class-one
    definition, Federer 3.1.1, p. 210, is intrinsic on its actual domain.
    No equality is required of arbitrary representatives outside it. *)
Lemma norm_class_one_field_unique (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (D E : X -> Hom X Y) :
  is_norm_class_one_field NX NY A f D ->
  is_norm_class_one_field NX NY A f E -> forall a, A a -> D a = E a.
Proof.
move=> hD hE a ha; exact: (norm_differential_unique hNX hNY
  (norm_class_one_differential hD ha) (norm_class_one_differential hE ha)).
Qed.

(** Source for [norm_field_continuous_operator]: exact operator-norm
    interpretation of derivative continuity in Federer 3.1.1, p. 210.
    Any values satisfying the abstract least-bound laws give the same
    epsilon continuity condition as uniform evaluation bounds. *)
Lemma norm_field_continuous_operator (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (A : X -> Prop) (D : X -> Hom X Y) (O : X -> X -> R) :
  (forall x a, A x -> A a -> is_norm_operator_norm NX NY (D x-D a) (O x a)) ->
  (norm_field_continuous NX NY A D <->
   forall a, A a -> forall e : R, 0 < e -> exists d : R, 0 < d /\
     forall h, A (a+h) -> NX h < d -> O (a+h) a < e).
Proof.
move=> hO; split.
- move=> hD a ha e he; have he2 : 0 < e/2 by lra.
  have [d [hd hb]] := hD a ha (e/2) he2.
  exists d; split=> // h hh hs.
  have hle := norm_operator_least (hO _ _ hh ha) (ltW he2) (hb h hh hs).
  by lra.
- move=> hD a ha e he; have [d [hd hb]] := hD a ha e he.
  exists d; split=> // h hh hs v.
  apply: le_trans (norm_operator_bound (hO _ _ hh ha) v) _.
  apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 v.
  exact: ltW (hb h hh hs).
Qed.
