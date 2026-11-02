(** Federer (1969), 3.1.11, p. 221:
    continuous affine polynomials are of class infinity.
    Their first differential is constant, so the result
    follows from the recursive class characterization. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormClassOneUP NormClassOneLaws ContinuousOperatorUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialFirst
  NormHigherDifferentialConstant NormClassHigherUP NormClassHigherLaws
  NormClassHigherArithmetic NormClassHigherFromDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section LinearSmoothness.
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

(** Source for [norm_class_infinity_linear]:
    the linear case of the continuous polynomial
    assertion in Federer 3.1.11, p. 221.
    The function is considered on any open
    domain, with its constant actual first differential. *)
Theorem norm_class_infinity_linear (L : Hom X Y) :
  norm_bounded_linear NX NY L ->
  norm_class_infinity NX NY ez ZN A L.
Proof.
move=> hL.
have hd a (ha : A a) := norm_differential_linear hNX hNY (@hA a ha) hL.
have hzero := norm_everywhere_differentiable_class_zero hNY hd.
have hop := continuous_multilinear_one_operator_space (@hZ 1%N).
have [z hz] := continuous_operator_surjective hop hL.
change (@continuous_multilinear_one_operator R X Y (Z 1%N) NX NY
  (@ez 1%N) (@ZN 1%N) (@hZ 1%N) z=L) in hz.
have hfirst a (ha : A a) :
    has_norm_higher_differential NX ez ZN A L 1%N a z.
  apply: (@norm_higher_differential_first R X Y NX NY hNX hNY Z ez ZN hZ A L a z).2.
  by rewrite hz; exact: hd a ha.
have hZN := continuous_multilinear_norm_is_norm hNY (@hZ 1%N).
pose W k := @ContinuousMultilinear.space R k X (Z 1%N) NX (@ZN 1%N) hNX hZN.
pose ew k := @ContinuousMultilinear.evaluation R k X (Z 1%N) NX (@ZN 1%N) hNX hZN.
pose WN k := @ContinuousMultilinear.norm R k X (Z 1%N) NX (@ZN 1%N) hNX hZN.
have hW k : is_continuous_multilinear_space NX (@ZN 1%N) (ew k) (WN k).
  exact: ContinuousMultilinear.laws.
have hc := @norm_class_infinity_constant R X (Z 1%N) NX (@ZN 1%N)
  hNX hZN W ew WN hW A hA z.
move=> [|k].
- exact ((@norm_class_higher_zero R X Y NX NY hNY Z ez ZN hZ A L).2 hzero).
- have hh := @norm_class_higher_from_derivative_field R 1%N k X Y NX NY
    hNX hNY Z ez ZN hZ W ew WN hW A L (fun _=>z) hzero hfirst (hc k).
  by rewrite add1n in hh.
Qed.

(** Source for [norm_class_infinity_affine]:
    continuous affine polynomials are smooth,
    the degree-at-most-one case of Federer 3.1.11,
    p. 221. Translation of the
    target adds only a constant polynomial. *)
Corollary norm_class_infinity_affine (L : Hom X Y) (c : Y) :
  norm_bounded_linear NX NY L ->
  norm_class_infinity NX NY ez ZN A (fun x=>L x+c).
Proof.
move=> hL k.
exact (@norm_class_higher_add R X Y NX NY hNX hNY Z ez ZN hZ A k L (fun _=>c)
  (norm_class_infinity_linear hL k)
  (@norm_class_infinity_constant R X Y NX NY hNX hNY Z ez ZN hZ A hA c k)).
Qed.
End LinearSmoothness.
