(** Federer (1969), 3.1.11, p. 221,
    and 3.1.13, p. 225:
    finite sums preserve all differentiability classes. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp functions.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialArithmetic
  NormHigherDifferentialConstant NormClassHigherUP NormClassHigherArithmetic
  NormClassHigherLocalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteSums.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.

(** Source for [norm_class_higher_finite_sum]:
    finite polynomial sums in Federer 3.1.11,
    p. 221, and the locally finite
    sum in 3.1.13, p. 225.
    The empty sum is the smooth zero function
    on the given open domain. *)
Theorem norm_class_higher_finite_sum (I : finType) (f : I->X->Y) k :
  (forall i, norm_class_higher NX NY ez ZN A (f i) k) ->
  norm_class_higher NX NY ez ZN A (fun x=>\sum_i f i x) k.
Proof.
move=> hf.
have hs : norm_class_higher NX NY ez ZN A (\sum_i f i) k.
  elim/big_ind: _=>[|g h hg hh|i _].
  - exact (@norm_class_infinity_constant R X Y NX NY hNX hNY Z ez ZN hZ A hA 0 k).
  - exact (norm_class_higher_add hNX hNY hZ hg hh).
  - exact: hf.
apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ A (\sum_i f i) (fun x=>\sum_i f i x) k _ hs).
move=>x _; by elim/big_rec2: _=>[|i y g _ <-].
Qed.

(** Source for [norm_class_infinity_finite_sum]:
    a finite sum of smooth functions is smooth,
    as used for the local expression of u
    in Federer 3.1.13, p. 225. *)
Corollary norm_class_infinity_finite_sum (I : finType) (f : I->X->Y) :
  (forall i, norm_class_infinity NX NY ez ZN A (f i)) ->
  norm_class_infinity NX NY ez ZN A (fun x=>\sum_i f i x).
Proof. move=>hf k; exact: norm_class_higher_finite_sum (fun i=>hf i k). Qed.
End FiniteSums.
