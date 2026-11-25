(** Federer (1969), 3.1.11, p. 219:
    transport between equal written arities of
    the same abstract multilinear space. This is
    equality substitution for grouping indices, not
    a new mathematical identification of spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ContinuousMultilinearUP NormHigherDifferentialUP
  MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [multilinear_degree_cast]:
    equality substitution for the arities p+q+1
    and p+(q+1), supporting the grouping identity
    in Federer 3.1.11, p. 219. *)
Definition multilinear_degree_cast (R : realType) (Z : nat->lmodType R)
    m n (h : m=n) : Hom (Z m) (Z n).
Proof.
subst n; apply: (@HomMap R (Z m) (Z m) (fun z=>z)).
by apply/asboolP=>c x y.
Defined.

(** Source for [multilinear_degree_cast_norm]:
    equal-degree transport preserves the supplied norm,
    supporting Federer 3.1.11, p. 219. *)
Lemma multilinear_degree_cast_norm (R : realType) (Z : nat->lmodType R)
    (ZN : forall k, Z k->R) m n (h : m=n) (z : Z m) :
  @ZN n (multilinear_degree_cast Z h z)=@ZN m z.
Proof. by subst n. Qed.

(** Source for [multilinear_degree_cast_evaluation]:
    transporting an equal arity in both the
    form and its argument tuple leaves the
    value unchanged, supporting Federer 3.1.11,
    p. 219. *)
Lemma multilinear_degree_cast_evaluation (R : realType)
    (X Y : lmodType R) (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    m n (h : m=n) (z : Z m) (u : {ffun 'I_m->X}) :
  @evaluation n (multilinear_arguments_cast h u) (multilinear_degree_cast Z h z)=
    @evaluation m u z.
Proof. subst n; by rewrite multilinear_arguments_cast_reflexive. Qed.

(** Source for [multilinear_degree_cast_inverse]:
    equal-arity transport is reversible, supporting
    the p+q indexing in Federer 3.1.11,
    p. 219. *)
Lemma multilinear_degree_cast_inverse (R : realType) (Z : nat->lmodType R)
    m n (h : m=n) (z : Z m) :
  multilinear_degree_cast Z (esym h) (multilinear_degree_cast Z h z)=z.
Proof. by subst n. Qed.

(** Source for [norm_higher_differential_degree_cast]:
    rewriting an equal natural-number order preserves
    the exact higher-differential graph, supporting
    the grouping formula in Federer 3.1.11,
    p. 219. *)
Lemma norm_higher_differential_degree_cast (R : realType)
    (X Y : lmodType R) (NX : X->R) (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R) (A : X->Prop) (f : X->Y)
    m n (h : m=n) a (z : Z m) :
  has_norm_higher_differential NX evaluation ZN A f m a z <->
  has_norm_higher_differential NX evaluation ZN A f n a (multilinear_degree_cast Z h z).
Proof. by subst n. Qed.


(** Source for [multilinear_degree_cast_inverse_right]:
    transporting a form back and then forward
    across equal arities fixes it, supporting
    the degree grouping in Federer 3.1.11,
    pp. 219–220. *)
Lemma multilinear_degree_cast_inverse_right (R : realType) (Z : nat->lmodType R)
    m n (h : m=n) (z : Z n) :
  multilinear_degree_cast Z h (multilinear_degree_cast Z (esym h) z)=z.
Proof. by subst n. Qed.
