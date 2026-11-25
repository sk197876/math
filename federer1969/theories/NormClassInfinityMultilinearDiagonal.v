(** Federer (1969), 3.1.11, p. 221:
    continuous homogeneous polynomials are smooth,
    including degree zero and infinite-dimensional
    normed source or target spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  NormHigherDifferentialConstant NormClassHigherUP NormClassHigherLocalValues
  NormClassInfinityLinear NormClassHigherDiagonalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section HomogeneousSmoothness.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ez : forall n, {ffun 'I_n->X}->Hom (Z n) Y.
Variable ZN : forall n, Z n->R.
Hypothesis hZ : forall n, is_continuous_multilinear_space NX NY (@ez n) (@ZN n).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.

(** Source for [norm_class_infinity_multilinear_diagonal]:
    a continuous homogeneous polynomial is of
    class infinity, as asserted in Federer
    3.1.11, p. 221.
    The proof applies the bilinear contraction
    laws repeatedly to a fixed abstract form. *)
Theorem norm_class_infinity_multilinear_diagonal n (z : Z n) :
  norm_class_infinity NX NY ez ZN A (fun x=>@ez n [ffun _ : 'I_n=>x] z).
Proof.
have hNn := continuous_multilinear_norm_is_norm hNY (@hZ n).
pose P j := @ContinuousMultilinear.space R j X X NX NX hNX hNX.
pose ep j := @ContinuousMultilinear.evaluation R j X X NX NX hNX hNX.
pose PN j := @ContinuousMultilinear.norm R j X X NX NX hNX hNX.
have hP j : is_continuous_multilinear_space NX NX (ep j) (PN j).
  exact: ContinuousMultilinear.laws.
pose W j := @ContinuousMultilinear.space R j X (Z n) NX (@ZN n) hNX hNn.
pose ew j := @ContinuousMultilinear.evaluation R j X (Z n) NX (@ZN n) hNX hNn.
pose WN j := @ContinuousMultilinear.norm R j X (Z n) NX (@ZN n) hNX hNn.
have hW j : is_continuous_multilinear_space NX (@ZN n) (ew j) (WN j).
  exact: ContinuousMultilinear.laws.
pose Id := hom_of_linear (linear_id X).
have hId : norm_bounded_linear NX NX Id.
  exists 1; split; first exact: ler01; by move=>x; rewrite /Id hom_of_linearE /= mul1r.
have hid := @norm_class_infinity_linear R X X NX NX hNX hNX P ep PN hP A hA Id hId.
have hc := @norm_class_infinity_constant R X (Z n) NX (@ZN n)
  hNX hNn W ew WN hW A hA z.
move=>k.
exact: (@norm_class_higher_diagonal_evaluation R X X Y NX NX NY hNX hNX hNY
  Z ez ZN hZ P Z ep PN ez ZN hP hZ A k n W ew WN hW
  (fun _=>z) Id (hc k) (hid k)).
Qed.

(** Source for [norm_class_infinity_bounded_multilinear_diagonal]:
    a continuous multilinear coefficient determines a
    smooth homogeneous polynomial, supporting the
    polynomial assertion of Federer 3.1.11, p. 221.
    The coefficient is represented only through
    the proved abstract-space surjectivity law. *)
Corollary norm_class_infinity_bounded_multilinear_diagonal n
    (f : {ffun 'I_n->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  norm_class_infinity NX NY ez ZN A (fun x=>f [ffun _ : 'I_n=>x]).
Proof.
move=>hf; have [z hz] := continuous_multilinear_surjective (@hZ n) hf.
have hc := norm_class_infinity_multilinear_diagonal z.
move=>k; apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ A (fun x=>@ez n [ffun _ : 'I_n=>x] z)
  (fun x=>f [ffun _ : 'I_n=>x]) k _ (hc k)).
by move=>x _; rewrite hz.
Qed.
End HomogeneousSmoothness.
