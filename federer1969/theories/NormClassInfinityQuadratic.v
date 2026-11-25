(** Federer (1969), 3.1.11, pp. 220–221:
    continuous quadratic polynomials are smooth.
    The bilinear closure theorem supplies the result
    without any choice of coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormBoundedBilinearUP
  NormClassHigherUP NormClassHigherBilinear NormClassInfinityLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_infinity_quadratic]:
    the continuous quadratic case of the polynomial
    smoothness assertion in Federer 3.1.11,
    p. 221, used for the radial
    cutoff of 3.1.13, p. 224. *)
Theorem norm_class_infinity_quadratic (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (B : X->X->Y) :
  (forall x, A x -> norm_domain_interior NX A x) ->
  norm_bounded_bilinear NX NX NY B ->
  norm_class_infinity NX NY ez ZN A (fun x=>B x x).
Proof.
move=> hA hB.
pose P j := @ContinuousMultilinear.space R j X X NX NX hNX hNX.
pose ep j := @ContinuousMultilinear.evaluation R j X X NX NX hNX hNX.
pose PN j := @ContinuousMultilinear.norm R j X X NX NX hNX hNX.
have hP j : is_continuous_multilinear_space NX NX (ep j) (PN j).
  exact: ContinuousMultilinear.laws.
pose Id := hom_of_linear (linear_id X).
have hId : norm_bounded_linear NX NX Id.
  exists 1; split; first exact: ler01.
  by move=> x; rewrite /Id hom_of_linearE /= mul1r.
have hidentity := @norm_class_infinity_linear R X X NX NX
  hNX hNX P ep PN hP A hA Id hId.
move=> k.
exact: (@norm_class_higher_bilinear R X NX hNX k X X Y
  NX NX NY hNX hNX hNY P P Z ep PN ep PN ez ZN hP hP hZ
  A Id Id B hB (hidentity k) (hidentity k)).
Qed.
