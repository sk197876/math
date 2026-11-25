(** Federer (1969), 3.1.11, pp. 219–221:
    linearity of higher differentials on their original
    domain, supporting polynomial differentiation and jets. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialArithmetic
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section HigherLinearCalculus.
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

(** Source for [norm_higher_differential_field_add]:
    higher differentials add, supporting the finite
    polynomial sums and Taylor jets in Federer 3.1.11,
    p. 221. The theorem uses exact differential
    fields on A, with no assumptions outside A. *)
Theorem norm_higher_differential_field_add k (f g : X->Y)
    (D E : X->Z k) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k x (D x)) ->
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A g k x (E x)) ->
  forall x, A x -> has_norm_higher_differential NX evaluation ZN A
    (fun t=>f t+g t) k x (D x+E x).
Proof.
elim: k D E=> [D E|k ih D E] hD hE x hx.
- split; first exact hx.
  by rewrite linearD /= (hD x hx).2 (hE x hx).2.
- have [P hP] := norm_higher_differential_field_previous hNX hNY hZ hD.
  have [Q hQ] := norm_higher_differential_field_previous hNX hNY hZ hE.
  have hsum := ih P Q hP hQ.
  have [L [hL hLe]] := norm_higher_differential_field_step_elim hNX hP (hD x hx).
  have [M [hM hMe]] := norm_higher_differential_field_step_elim hNX hQ (hE x hx).
  apply: (norm_higher_differential_field_step hNX hNY hZ hsum
    (norm_differential_add (continuous_multilinear_norm_is_norm hNY (@hZ k)) hL hM)).
  by move=> u v; rewrite hom_addE !linearD /= hLe hMe.
Qed.

(** Source for [norm_higher_differential_field_scale]:
    scalar multiples commute with every higher
    differential, supporting the Taylor coefficients in
    Federer 3.1.11, p. 221. The scalar zero
    is included without division. *)
Theorem norm_higher_differential_field_scale k (f : X->Y)
    (D : X->Z k) (c : R) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k x (D x)) ->
  forall x, A x -> has_norm_higher_differential NX evaluation ZN A
    (fun t=>c*:f t) k x (c*:D x).
Proof.
elim: k D=> [D|k ih D] hD x hx.
- split; first exact hx; by rewrite linearZ /= (hD x hx).2.
- have [P hP] := norm_higher_differential_field_previous hNX hNY hZ hD.
  have hscaled := ih P hP.
  have [L [hL hLe]] := norm_higher_differential_field_step_elim hNX hP (hD x hx).
  apply: (norm_higher_differential_field_step hNX hNY hZ hscaled
    (norm_differential_scale hNX (continuous_multilinear_norm_is_norm hNY (@hZ k)) c hL)).
  by move=> u v; rewrite hom_scaleE !linearZ /= hLe.
Qed.
End HigherLinearCalculus.
