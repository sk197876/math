(** Federer (1969), 3.1.1, p. 210: classes zero and one on open
    domains. Derivative continuity is stated by uniform homogeneous
    evaluation bounds, the epsilon form of operator-norm continuity. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_zero]: a continuous function on an open
    subset of a normed space, Federer 3.1.1, p. 210. The domain is explicit
    and continuity uses the supplied norms, with no extension requirement. *)
Definition norm_class_zero (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y) :=
  forall a, A a -> norm_domain_interior NX A a /\
    forall e : R, 0 < e -> exists d : R, 0 < d /\
      forall h, A (a+h) -> NX h < d -> NY (f (a+h)-f a) < e.

(** Source for [norm_field_continuous]: continuity of Df in the
    operator norm, Federer 3.1.1, p. 210, expressed by its uniform
    homogeneous evaluation bounds. NormClassOneLaws proves the
    equivalence with the least-bound operator-norm specification. *)
Definition norm_field_continuous (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (D : X -> Hom X Y) :=
  forall a, A a -> forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall h, A (a+h) -> NX h < d -> forall v,
      NY ((D (a+h)-D a) v) <= e*NX v.

(** Source for [is_norm_class_one_field]: the class-one conditions of
    Federer 3.1.1, p. 210, with an explicit candidate derivative field.
    The field must be the actual differential at every domain point. *)
Record is_norm_class_one_field (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (D : X -> Hom X Y) : Prop := {
  (** Source for [norm_class_one_zero]: class one implies class zero,
      Federer 3.1.1, p. 210. *)
  norm_class_one_zero : norm_class_zero NX NY A f;
  (** Source for [norm_class_one_differential]: existence of Df at
      every domain point, Federer 3.1.1, p. 210. *)
  norm_class_one_differential : forall a, A a ->
    has_norm_differential NX NY A f a (D a);
  (** Source for [norm_class_one_continuity]: continuity of Df in the
      norm of continuous linear maps, Federer 3.1.1, p. 210. *)
  norm_class_one_continuity : norm_field_continuous NX NY A D
}.

(** Source for [norm_class_one]: class one, Federer 3.1.1, p. 210.
    Existence of a derivative field is required, and all of its defining
    laws must be proved; this definition introduces no project axiom. *)
Definition norm_class_one (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y) :=
  exists D : X -> Hom X Y, is_norm_class_one_field NX NY A f D.
