(** Federer (1969), 3.1.11, p. 221:
    constant polynomials have zero positive-order
    differentials and are of class infinity. This is
    the degree-zero case of the polynomial assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearZero NormHigherDifferentialUP NormHigherDifferentialFields
  NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [constant_higher_form]: the constant
    polynomial has its value in degree zero and zero
    in positive degrees, supporting the polynomial statement
    in Federer 3.1.11, p. 221. *)
Definition constant_higher_form (R : realType) (Z : nat->lmodType R)
    (c : Z 0%N) (k : nat) : Z k :=
  match k as j return Z j with 0%N=>c | j.+1=> 0 end.

Section ConstantDifferentials.
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
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.

(** Source for [norm_higher_differential_constant]:
    all positive-order differentials of a constant
    polynomial vanish, the degree-zero case of Federer
    3.1.11, p. 221. The original domain is
    any open set, including the empty set. *)
Theorem norm_higher_differential_constant (c : Y) (c0 : Z 0%N) :
  @evaluation 0%N [ffun i : 'I_0=>(0:X)] c0=c ->
  forall k a, A a ->
    has_norm_higher_differential NX evaluation ZN A (fun _=>c) k a
      (@constant_higher_form R Z c0 k).
Proof.
move=> hc; elim=> [|k ih] a ha.
- by split.
- apply: (@norm_higher_differential_field_step R X Y NX NY hNX hNY
    Z evaluation ZN hZ A (fun _=>c) k
    (fun _=>@constant_higher_form R Z c0 k) a 0 0).
  + exact ih.
  + have hh := norm_differential_constant hNX
      (continuous_multilinear_norm_is_norm hNY (@hZ k))
      (@constant_higher_form R Z c0 k) (@hA a ha).
    exact hh.
  + by move=> u v; rewrite hom_zeroE !linear0.
Qed.

(** Source for [norm_class_infinity_constant]:
    a degree-zero polynomial is of class infinity,
    the constant case of Federer 3.1.11, p. 221.
    No completeness, finite dimension or nonempty domain is required. *)
Theorem norm_class_infinity_constant (c : Y) :
  norm_class_infinity NX NY evaluation ZN A (fun _=>c).
Proof.
have [c0 hc0] := continuous_multilinear_zero_surjective hNY (@hZ 0%N) c.
move=> k; split.
- move=> a ha; split; first exact: @hA a ha.
  move=> e he; exists 1; split; first exact: ltr01.
  by move=> h _ _; rewrite subrr (real_seminorm_zero hNY.1).
- exists (fun _=>@constant_higher_form R Z c0 k); split.
  + exact (@norm_higher_differential_constant c c0 hc0 k).
  + move=> a ha; split; first exact: @hA a ha.
    move=> e he; exists 1; split; first exact: ltr01.
    move=> h _ _; rewrite subrr.
    by rewrite (real_seminorm_zero
      (continuous_multilinear_norm_is_norm hNY (@hZ k)).1).
Qed.
End ConstantDifferentials.
