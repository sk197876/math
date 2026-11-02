(** Federer (1969), 3.1.21, p. 234: one derivative of
    regularity is lost in the tangent and normal bundle charts.
    This adapter uses the proved class calculus of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearOne ContinuousMultilinearSealed NormDifferentialUP NormRegularity
  NormClassHigherUP NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherFields NormClassHigherDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Derivatives.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ev := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).

(** Source for [norm_class_derivative_field]: supporting
    regularity of x -> Df(x) in the tangent-bundle assertion
    of Federer 3.1.21, p. 234, from 3.1.11, p. 221.
    A class-(k+1) map has an actual derivative representative
    of class k in the public sealed operator space. *)
Lemma norm_class_derivative_field (A:X->Prop) (f:X->Y) k :
  norm_class hNX hNY A f k.+1 -> exists G:X->Z 1%N,
    norm_class hNX hN1 A G k /\ forall a,A a ->
      has_norm_differential NX NY A f a
        (@continuous_multilinear_one_operator R X Y (Z 1%N) NX NY
          (@ev 1%N) (@ZN 1%N) (hZ 1%N) (G a)).
Proof.
move=>hf.
have [D [hD hcD]]:=@norm_class_higher_fields R X Y NX NY hNX hNY Z ev ZN hZ A f k.+1 hf.
have h1: (1<=k.+1)%N by [].
have hG a (ha:A a):has_norm_higher_differential NX ev ZN A f 1%N a (D 1%N a).
  exact: hD 1%N h1 a ha.
exists (D 1%N); split.
- have hk:@norm_class_higher R X Y NX NY Z ev ZN A f (1+k)%N by rewrite add1n.
  exact (@norm_class_higher_derivative_field R 1%N k X Y NX NY hNX hNY Z ev ZN hZ
    (fun j=>@ContinuousMultilinear.space R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
    (fun j=>@ContinuousMultilinear.evaluation R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
    (fun j=>@ContinuousMultilinear.norm R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
    (fun j=>@ContinuousMultilinear.laws R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
    A f (D 1%N) hk hG).
- move=>a ha; exact: (@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A f a (D 1%N a)).1 (hG a ha).
Qed.
End Derivatives.
