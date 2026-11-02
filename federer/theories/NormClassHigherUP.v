(** Federer (1969), 3.1.11, p. 220:
    class k means that the kth differential exists everywhere
    on the open domain and is continuous. The supplied field
    is required to be the exact recursively defined differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormClassOneUP NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_norm_higher_differential_field]:
    the exact field D^k f on the domain in Federer
    3.1.11, p. 220. Its total representative outside
    the domain is immaterial. *)
Definition is_norm_higher_differential_field (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R) (A : X->Prop) (f : X->Y) k (D : X->Z k) :=
  forall a, A a -> has_norm_higher_differential NX evaluation ZN A f k a (D a).

(** Source for [norm_class_higher]: a function of class k
    is of class zero, is k times differentiable on its domain,
    and has a continuous kth differential,
    Federer 3.1.11, p. 220. Existence is part of
    this predicate and must be proved for each function;
    no existence axiom is introduced. *)
Definition norm_class_higher (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R) (A : X->Prop) (f : X->Y) k :=
  norm_class_zero NX NY A f /\
  exists D : X->Z k,
    is_norm_higher_differential_field NX evaluation ZN A f D /\
    norm_class_zero NX (@ZN k) A D.

(** Source for [norm_class_infinity]: class infinity means
    class k for every natural number k, as in Federer
    3.1.11, pp. 220–223. *)
Definition norm_class_infinity (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R) (A : X->Prop) (f : X->Y) :=
  forall k, norm_class_higher NX NY evaluation ZN A f k.
