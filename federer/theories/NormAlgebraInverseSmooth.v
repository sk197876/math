(** Federer (1969), 3.1.11, p. 220:
    inversion is infinitely differentiable on the
    open set of invertible elements of a Banach
    algebra. The proof bootstraps the established
    first derivative through bounded bilinear calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom AlgebraUP RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP AlgebraInverseUP AlgebraInverse NormDifferentialUP
  NormClassOneUP NormAlgebraInverseDifferential NormAlgebraInverseClassOne
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousMultilinearSealed AlgebraSandwichOperator NormHigherDifferentialUP
  NormHigherDifferentialFirst NormClassHigherUP NormClassHigherLaws
  NormClassHigherArithmetic NormClassHigherBilinear NormClassHigherFromDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_algebra_inverse_class_infinity]:
    the infinite differentiability of inversion used
    in Federer 3.1.11, p. 220.
    The exact inverse domain is the domain of
    the sealed two-sided-inverse graph. The total
    representative is constrained only there.
    Completeness is used for the inverse's open
    domain and first derivative, not postulated
    for any derivative-space construction. *)
Theorem norm_algebra_inverse_class_infinity (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->A}->Hom (Z k) A)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space N N (@ez k) (@ZN k))
    (F : A->A)
    (hF : forall x, partial_function_domain (algebra_inverse A) x ->
      is_two_sided_algebra_inverse x (F x)) :
  norm_class_infinity N N ez ZN (partial_function_domain (algebra_inverse A)) F.
Proof.
pose U := partial_function_domain (algebra_inverse A).
have hzero := norm_class_one_zero (@norm_algebra_inverse_class_one_field R A N hN hM hcomplete F hF).
have hZN := continuous_multilinear_norm_is_norm hN (@hZ 1%N).
have [B [hB hBE]] := algebra_sandwich_operator_exists hN hM (@hZ 1%N).
pose D x := (-1 : R)*:B (F x) (F x).
have hD x (hx : U x) :
    has_norm_higher_differential N ez ZN U F 1%N x (D x).
  apply: (@norm_higher_differential_first R A A N N hN hN Z ez ZN hZ U F x (D x)).2.
  have he : @continuous_multilinear_one_operator R A A (Z 1%N) N N
      (@ez 1%N) (@ZN 1%N) (@hZ 1%N) (D x)=algebra_inverse_linear_term (F x).
    apply: hom_ext=>v.
    change (@ez 1%N [ffun _ : 'I_1=>v] ((-1 : R)*:B (F x) (F x))=
      -alg_mul A (F x) (alg_mul A v (F x))).
    by rewrite linearZ /= hBE scaleNr scale1r.
  rewrite he; exact (@norm_algebra_inverse_differential R A N hN hM hcomplete F hF x hx).
pose W k := @ContinuousMultilinear.space R k A (Z 1%N) N (@ZN 1%N) hN hZN.
pose ew k := @ContinuousMultilinear.evaluation R k A (Z 1%N) N (@ZN 1%N) hN hZN.
pose WN k := @ContinuousMultilinear.norm R k A (Z 1%N) N (@ZN 1%N) hN hZN.
have hW k : is_continuous_multilinear_space N (@ZN 1%N) (ew k) (WN k).
  exact: ContinuousMultilinear.laws.
change (forall k, norm_class_higher N N ez ZN U F k).
elim=>[|k ih].
- exact ((@norm_class_higher_zero R A A N N hN Z ez ZN hZ U F).2 hzero).
- have hBB := @norm_class_higher_bilinear R A N hN k
    A A (Z 1%N) N N (@ZN 1%N) hN hN hZN Z Z W
    ez ZN ez ZN ew WN hZ hZ hW U F F B hB ih ih.
  have hDC : norm_class_higher N (@ZN 1%N) ew WN U D k.
    exact: (@norm_class_higher_scale R A (Z 1%N) N (@ZN 1%N)
      hN hZN W ew WN hW U k (fun x=>B (F x) (F x)) (-1) hBB).
  have hh := @norm_class_higher_from_derivative_field R 1%N k A A N N
    hN hN Z ez ZN hZ W ew WN hW U F D hzero hD hDC.
  by rewrite add1n in hh.
Qed.
