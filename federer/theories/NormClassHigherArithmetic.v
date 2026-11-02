(** Federer (1969), 3.1.11, pp. 220–221:
    classes k are closed under finite linear operations,
    supporting the polynomial and jet assertions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormClassOneUP NormClassZeroArithmetic
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialArithmetic NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section HigherClassArithmetic.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A : X->Prop.

(** Source for [norm_class_higher_add]: sums preserve
    class k, supporting the polynomial and Taylor-jet
    statements in Federer 3.1.11, p. 221. *)
Theorem norm_class_higher_add k (f g : X->Y) :
  norm_class_higher NX NY evaluation ZN A f k ->
  norm_class_higher NX NY evaluation ZN A g k ->
  norm_class_higher NX NY evaluation ZN A (fun x=>f x+g x) k.
Proof.
move=> [hf [D [hD hDc]]] [hg [E [hE hEc]]].
split; first exact (norm_class_zero_add hNY hf hg).
exists (fun x=>D x+E x); split.
- exact (norm_higher_differential_field_add hNX hNY hZ hD hE).
- exact (norm_class_zero_add
    (continuous_multilinear_norm_is_norm hNY (@hZ k)) hDc hEc).
Qed.

(** Source for [norm_class_higher_scale]: scalar multiples
    preserve class k, supporting the factorial coefficients
    in the Taylor jets of Federer 3.1.11, p. 221. *)
Theorem norm_class_higher_scale k (f : X->Y) (c : R) :
  norm_class_higher NX NY evaluation ZN A f k ->
  norm_class_higher NX NY evaluation ZN A (fun x=>c*:f x) k.
Proof.
move=> [hf [D [hD hDc]]].
split; first exact (norm_class_zero_scale hNY c hf).
exists (fun x=>c*:D x); split.
- exact (norm_higher_differential_field_scale hNX hNY hZ c hD).
- exact (norm_class_zero_scale
    (continuous_multilinear_norm_is_norm hNY (@hZ k)) c hDc).
Qed.
End HigherClassArithmetic.
