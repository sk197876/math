(** Federer (1969), 3.1.18, p. 229: differentiability classes of maps
    between arbitrary normed spaces. This representation wrapper uses the
    opaque continuous multilinear spaces of 3.1.11, pp. 218–220; it does
    not choose coordinates or expose their existence constructions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearSealed NormClassOneUP NormClassHigherUP
  NormClassHigherLaws NormClassHigherFirst.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Regularity.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ev := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).

(** Source for [norm_class]: the class-k convention recalled in Federer
    3.1.18, p. 229, with the abstract multilinear representation of 3.1.11.
    This is the previously proved higher-class predicate instantiated in
    the public sealed operator spaces, not a new regularity condition. *)
Definition norm_class (A : X->Prop) (f : X->Y) (k : nat) :=
  @norm_class_higher R X Y NX NY Z ev ZN A f k.

(** Source for [norm_class_all_orders]: class infinity in 3.1.11,
    p. 220, as used for smooth changes of coordinates after 3.1.18,
    p. 229. The same map and domain have every finite class. *)
Definition norm_class_all_orders (A : X->Prop) (f : X->Y) :=
  forall k, norm_class A f k.

(** Source for [norm_class_zeroP]: the class-zero convention of 3.1.1,
    p. 210, supporting the diffeomorphism definition in Federer 3.1.18,
    p. 229. It is continuity on the actual open domain. *)
Lemma norm_class_zeroP (A : X->Prop) (f : X->Y) :
  norm_class A f 0%N <-> norm_class_zero NX NY A f.
Proof.
exact (@norm_class_higher_zero R X Y NX NY hNY Z ev ZN
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) A f).
Qed.

(** Source for [norm_class_firstP]: the class-one convention of 3.1.1,
    p. 210, supporting the diffeomorphism definition in Federer 3.1.18,
    p. 229. The abstract representation agrees with the actual first
    differential and its continuity. *)
Lemma norm_class_firstP (A : X->Prop) (f : X->Y) :
  norm_class A f 1%N <-> norm_class_one NX NY A f.
Proof.
exact (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) A f).
Qed.

(** Source for [norm_class_lower]: lowering differentiability class,
    Federer 3.1.11, p. 220, used in 3.1.18, p. 229. *)
Lemma norm_class_lower (A : X->Prop) (f : X->Y) k j :
  (j<=k)%N -> norm_class A f k -> norm_class A f j.
Proof.
exact (@norm_class_higher_lower R X Y NX NY hNX hNY Z ev ZN
  (fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY) A f k j).
Qed.

(** Source for [norm_class_continuous]: every class includes continuity,
    Federer 3.1.11, p. 220, used in the diffeomorphism definition of
    3.1.18, p. 229. *)
Lemma norm_class_continuous (A : X->Prop) (f : X->Y) k :
  norm_class A f k -> norm_class_zero NX NY A f.
Proof. by move=>[hf _]. Qed.
End Regularity.
Arguments norm_class {R X Y NX NY} hNX hNY A f k.
Arguments norm_class_all_orders {R X Y NX NY} hNX hNY A f.
