(** Federer (1969), 3.1.11, p. 223:
    the exponential is of class infinity, a scalar
    ingredient of the printed smooth cutoff. Every
    derivative coefficient is the exponential itself. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP RealExponentialUP RealExponentialSealed
  RealExponentialDifferential ContinuousMultilinearUP NormHigherDifferentialUP
  NormClassHigherUP ScalarDerivativeSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SmoothExponential.
Variable R : realType.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->R^o}->Hom (Z k) R^o.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@evaluation k) (@ZN k).
Local Notation E := (@RealExponential.exponential R).

(** Source for [real_exponential_higher_differentials]:
    the scalar exponential used in Federer 3.1.11,
    p. 223, has its own value as every ordinary
    derivative coefficient. The higher multilinear formula
    is the real-source identification of p. 220. *)
Theorem real_exponential_higher_differentials k a :
  exists z : Z k,
    has_norm_higher_differential (fun t : R^o=>`|t|) evaluation ZN
      (fun _=>True) E k a z /\
    forall u, @evaluation k u z=(\prod_(i<k) u i)*E a.
Proof.
have hseq (n : nat) b (_ : True) : exists L : Hom R^o R^o,
    has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      (fun _=>True) E b L /\ forall t, L t=t*E b.
  exists (real_exponential_linear_term b); split.
  - exact: real_exponential_differential.
  - by move=> t; change (E b*t=t*E b); rewrite mulrC.
have [D [hD [hDe _]]] := @scalar_derivative_sequence_differentials R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R) Z evaluation ZN hZ
  (fun _=>True) (fun _ : nat=>E) hseq.
exists (D k a); split; first exact: hD k a I.
exact: hDe.
Qed.

(** Source for [real_exponential_class_infinity]:
    the exponential ingredient of the class-infinity
    scalar example in Federer 3.1.11, p. 223,
    obtained entirely from the sealed scalar laws. *)
Theorem real_exponential_class_infinity :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    evaluation ZN (fun _=>True) E.
Proof.
apply: (@scalar_derivative_sequence_class_infinity R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R) Z evaluation ZN hZ
  (fun _=>True) (fun _ : nat=>E)).
move=> n a _; exists (real_exponential_linear_term a); split.
- exact: real_exponential_differential.
- by move=> t; change (E a*t=t*E a); rewrite mulrC.
Qed.
End SmoothExponential.
