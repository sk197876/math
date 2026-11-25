(** Federer (1969), 3.1.11, p. 221,
    and 3.1.13, p. 225:
    every higher differential commutes with finite sums.
    This is the local algebraic step for the
    derivatives of the partition denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialConstant NormHigherDifferentialArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteDerivativeSums.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.

(** Source for [norm_higher_differential_sequence_sum]:
    finite sums of actual differential fields,
    supporting D^i sigma=sum_s D^i u_s
    in Federer 3.1.13, p. 225,
    and the finite polynomials in 3.1.11,
    p. 221. Repeated indices are allowed. *)
Theorem norm_higher_differential_sequence_sum (J : Type)
    (f : J->X->Y) k (D : J->X->Z k) :
  (forall j x, A x -> has_norm_higher_differential NX ev ZN A (f j) k x (D j x)) ->
  forall r : seq J, forall x, A x ->
    has_norm_higher_differential NX ev ZN A
      (fun y=>\sum_(j<-r) f j y) k x (\sum_(j<-r) D j x).
Proof.
move=>hD; elim=>[|j r ih] x hx.
- have he : (fun y : X=>\sum_(j<-[::]) f j y)=(fun _=>0).
    by apply/funext=>y; rewrite big_nil.
  rewrite he big_nil.
  have he0 : @ev 0%N [ffun i : 'I_0=>(0:X)] 0=0 by rewrite linear0.
  have hz := @norm_higher_differential_constant R X Y NX NY hNX hNY
    Z ev ZN hZ A hA 0 0 he0 k x hx.
  have hcf : forall n, @constant_higher_form R Z 0 n=0 by case.
  by rewrite hcf in hz.
- have hcons : (fun y : X=>\sum_(i<-j::r) f i y)=(fun y=>f j y+\sum_(i<-r) f i y).
    by apply/funext=>y; rewrite big_cons.
  rewrite hcons big_cons.
  exact: (norm_higher_differential_field_add hNX hNY hZ (hD j) ih hx).
Qed.

(** Source for [norm_higher_differential_finite_sum]:
    the finite-index version used for local
    partition sums, Federer 3.1.13, p. 225.
    It includes an empty index type. *)
Corollary norm_higher_differential_finite_sum (J : finType)
    (f : J->X->Y) k (D : J->X->Z k) :
  (forall j x, A x -> has_norm_higher_differential NX ev ZN A (f j) k x (D j x)) ->
  forall x, A x ->
    has_norm_higher_differential NX ev ZN A
      (fun y=>\sum_j f j y) k x (\sum_j D j x).
Proof. move=>hD; exact: (norm_higher_differential_sequence_sum hD (index_enum J)). Qed.
End FiniteDerivativeSums.
