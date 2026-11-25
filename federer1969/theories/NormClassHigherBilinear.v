(** Federer (1969), 3.1.11, p. 220:
    every continuous bilinear operation preserves class k.
    This supplies the bilinear induction step used for
    higher composition and inversion. The derivative
    spaces are abstract; auxiliary hierarchies are obtained
    through the opaque continuous-multilinear interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  ContinuousMultilinearBilinearLift NormBoundedBilinearUP
  NormClassZeroBilinear NormHigherBilinearFirstField
  NormClassHigherUP NormClassHigherLaws NormClassHigherArithmetic
  NormClassHigherDerivative NormClassHigherFromDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section HigherBilinearCalculus.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.

(** Source for [norm_class_higher_bilinear]:
    the continuous bilinear step in the induction
    for maps of class k, Federer 3.1.11,
    p. 220. In particular it applies
    to composition of bounded linear maps and
    to multiplication in a normed algebra.
    No finite-dimensional or completeness hypothesis
    is imposed on the normed spaces. *)
Theorem norm_class_higher_bilinear k :
  forall (U V W : lmodType R)
    (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (P Q S : nat->lmodType R)
    (ep : forall j, {ffun 'I_j->X}->Hom (P j) U) (PN : forall j, P j->R)
    (eq : forall j, {ffun 'I_j->X}->Hom (Q j) V) (QN : forall j, Q j->R)
    (es : forall j, {ffun 'I_j->X}->Hom (S j) W) (SN : forall j, S j->R)
    (hP : forall j, is_continuous_multilinear_space NX NU (@ep j) (@PN j))
    (hQ : forall j, is_continuous_multilinear_space NX NV (@eq j) (@QN j))
    (hS : forall j, is_continuous_multilinear_space NX NW (@es j) (@SN j))
    (A : X->Prop) (f : X->U) (g : X->V) (B : U->V->W),
  norm_bounded_bilinear NU NV NW B ->
  norm_class_higher NX NU ep PN A f k ->
  norm_class_higher NX NV eq QN A g k ->
  norm_class_higher NX NW es SN A (fun x=>B (f x) (g x)) k.
Proof.
elim: k=>[|k ih] U V W NU NV NW hNU hNV hNW P Q S
  ep PN eq QN es SN hP hQ hS A f g B hB hf hg.
- apply: (@norm_class_higher_zero R X W NX NW hNW S es SN hS
    A (fun x=>B (f x) (g x))).2.
  exact (norm_class_zero_bilinear hNU hNV hNW hB hf.1 hg.1).
- have hzero := norm_class_zero_bilinear hNU hNV hNW hB hf.1 hg.1.
  have hfprev := norm_class_higher_previous hNX hNU hP hf.
  have hgprev := norm_class_higher_previous hNX hNV hQ hg.
  have h1 : (1<=k.+1)%N by [].
  have [_ [F [hF hcF]]] := @norm_class_higher_lower R X U NX NU
    hNX hNU P ep PN hP A f k.+1 1%N h1 hf.
  have [_ [G [hG hcG]]] := @norm_class_higher_lower R X V NX NV
    hNX hNV Q eq QN hQ A g k.+1 1%N h1 hg.
  have hPN := continuous_multilinear_norm_is_norm hNU (@hP 1%N).
  have hQN := continuous_multilinear_norm_is_norm hNV (@hQ 1%N).
  have hSN := continuous_multilinear_norm_is_norm hNW (@hS 1%N).
  pose PF j := @ContinuousMultilinear.space R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose epF j := @ContinuousMultilinear.evaluation R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose PNF j := @ContinuousMultilinear.norm R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  have hPF j : is_continuous_multilinear_space NX (@PN 1%N) (epF j) (PNF j).
    exact: ContinuousMultilinear.laws.
  pose QF j := @ContinuousMultilinear.space R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose eqF j := @ContinuousMultilinear.evaluation R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose QNF j := @ContinuousMultilinear.norm R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  have hQF j : is_continuous_multilinear_space NX (@QN 1%N) (eqF j) (QNF j).
    exact: ContinuousMultilinear.laws.
  pose SF j := @ContinuousMultilinear.space R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose esF j := @ContinuousMultilinear.evaluation R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose SNF j := @ContinuousMultilinear.norm R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  have hSF j : is_continuous_multilinear_space NX (@SN 1%N) (esF j) (SNF j).
    exact: ContinuousMultilinear.laws.
  have hf1k : norm_class_higher NX NU ep PN A f (1+k)%N by rewrite add1n.
  have hg1k : norm_class_higher NX NV eq QN A g (1+k)%N by rewrite add1n.
  have hFk := @norm_class_higher_derivative_field R 1%N k X U NX NU hNX hNU
    P ep PN hP PF epF PNF hPF A f F hf1k hF.
  have hGk := @norm_class_higher_derivative_field R 1%N k X V NX NV hNX hNV
    Q eq QN hQ QF eqF QNF hQF A g G hg1k hG.
  have [CF [hCF heF]] := @continuous_multilinear_bilinear_first_lift
    R 1%N X U V W (P 1%N) (S 1%N) NX NU NV NW hNV
    (@ep 1%N) (@PN 1%N) (@es 1%N) (@SN 1%N) (@hP 1%N) (@hS 1%N) B hB.
  have [CG [hCG heG]] := @continuous_multilinear_bilinear_second_lift
    R 1%N X U V W (Q 1%N) (S 1%N) NX NU NV NW hNU
    (@eq 1%N) (@QN 1%N) (@es 1%N) (@SN 1%N) (@hQ 1%N) (@hS 1%N) B hB.
  pose H x := CF (F x) (g x)+CG (f x) (G x).
  have hH := @norm_higher_first_bilinear_field R X U V W NX NU NV NW
    hNX hNU hNV hNW P Q S ep PN eq QN es SN hP hQ hS
    B CF CG A f g F G hB heF heG hF hG.
  have hFC := ih (P 1%N) V (S 1%N) (@PN 1%N) NV (@SN 1%N)
    hPN hNV hSN PF Q SF epF PNF eq QN esF SNF hPF hQ hSF
    A F g CF hCF hFk hgprev.
  have hGC := ih U (Q 1%N) (S 1%N) NU (@QN 1%N) (@SN 1%N)
    hNU hQN hSN P QF SF ep PN eqF QNF esF SNF hP hQF hSF
    A f G CG hCG hfprev hGk.
  have hHC : norm_class_higher NX (@SN 1%N) esF SNF A H k.
    exact (norm_class_higher_add hNX hSN hSF hFC hGC).
  have hresult := @norm_class_higher_from_derivative_field R 1%N k X W
    NX NW hNX hNW S es SN hS SF esF SNF hSF
    A (fun x=>B (f x) (g x)) H hzero hH hHC.
  by rewrite add1n in hresult.
Qed.
End HigherBilinearCalculus.
