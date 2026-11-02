(** Federer (1969), 3.1.11, p. 220:
    composition preserves class k. The proof follows
    the printed induction using the first chain rule,
    bilinearity of operator composition, and the exact
    recursive derivative fields. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialChain
  NormClassOneUP ContinuousOperatorUP ContinuousOperatorComposition
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialFirst
  NormClassHigherUP NormClassHigherLaws NormClassHigherDerivative
  NormClassHigherFromDerivative NormClassHigherRestriction
  NormClassZeroComposition NormClassHigherBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section HigherComposition.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.

(** Source for [norm_class_higher_composition]:
    Federer 3.1.11, p. 220:
    the composition of maps of class k
    is of class k. The domain is
    the actual composite domain A intersect
    f inverse(B), and no global inclusion,
    finite-dimensionality or completeness is assumed. *)
Theorem norm_class_higher_composition k :
  forall (Y Z : lmodType R) (NY : Y->R) (NZ : Z->R)
    (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (P Q S : nat->lmodType R)
    (ep : forall j, {ffun 'I_j->X}->Hom (P j) Y) (PN : forall j, P j->R)
    (eq : forall j, {ffun 'I_j->Y}->Hom (Q j) Z) (QN : forall j, Q j->R)
    (es : forall j, {ffun 'I_j->X}->Hom (S j) Z) (SN : forall j, S j->R)
    (hP : forall j, is_continuous_multilinear_space NX NY (@ep j) (@PN j))
    (hQ : forall j, is_continuous_multilinear_space NY NZ (@eq j) (@QN j))
    (hS : forall j, is_continuous_multilinear_space NX NZ (@es j) (@SN j))
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->Z),
  norm_class_higher NX NY ep PN A f k ->
  norm_class_higher NY NZ eq QN B g k ->
  norm_class_higher NX NZ es SN (fun x=>A x /\ B (f x)) (fun x=>g (f x)) k.
Proof.
elim: k=>[|k ih] Y Z NY NZ hNY hNZ P Q S ep PN eq QN es SN
  hP hQ hS A B f g hf hg.
- apply: (@norm_class_higher_zero R X Z NX NZ hNZ S es SN hS
    (fun x=>A x /\ B (f x)) (fun x=>g (f x))).2.
  exact (norm_class_zero_composition hf.1 hg.1).
- pose C x := A x /\ B (f x).
  have hzero := norm_class_zero_composition hf.1 hg.1.
  have hopen a (ha : C a) : norm_domain_interior NX C a := (hzero a ha).1.
  have hCA x : C x -> A x by move=> [hx _].
  have hfprev := norm_class_higher_previous hNX hNY hP hf.
  have h1 : (1<=k.+1)%N by [].
  have [_ [F [hF hcF]]] := @norm_class_higher_lower R X Y NX NY
    hNX hNY P ep PN hP A f k.+1 1%N h1 hf.
  have [_ [G [hG hcG]]] := @norm_class_higher_lower R Y Z NY NZ
    hNY hNZ Q eq QN hQ B g k.+1 1%N h1 hg.
  have hPN := continuous_multilinear_norm_is_norm hNY (@hP 1%N).
  have hQN := continuous_multilinear_norm_is_norm hNZ (@hQ 1%N).
  have hSN := continuous_multilinear_norm_is_norm hNZ (@hS 1%N).
  pose PF j := @ContinuousMultilinear.space R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose epF j := @ContinuousMultilinear.evaluation R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose PNF j := @ContinuousMultilinear.norm R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  have hPF j : is_continuous_multilinear_space NX (@PN 1%N) (epF j) (PNF j).
    exact: ContinuousMultilinear.laws.
  pose QF j := @ContinuousMultilinear.space R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  pose eqF j := @ContinuousMultilinear.evaluation R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  pose QNF j := @ContinuousMultilinear.norm R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  have hQF j : is_continuous_multilinear_space NY (@QN 1%N) (eqF j) (QNF j).
    exact: ContinuousMultilinear.laws.
  pose T j := @ContinuousMultilinear.space R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose et j := @ContinuousMultilinear.evaluation R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  pose TN j := @ContinuousMultilinear.norm R j X (Q 1%N) NX (@QN 1%N) hNX hQN.
  have hT j : is_continuous_multilinear_space NX (@QN 1%N) (et j) (TN j).
    exact: ContinuousMultilinear.laws.
  pose SF j := @ContinuousMultilinear.space R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose esF j := @ContinuousMultilinear.evaluation R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  pose SNF j := @ContinuousMultilinear.norm R j X (S 1%N) NX (@SN 1%N) hNX hSN.
  have hSF j : is_continuous_multilinear_space NX (@SN 1%N) (esF j) (SNF j).
    exact: ContinuousMultilinear.laws.
  have hf1k : norm_class_higher NX NY ep PN A f (1+k)%N by rewrite add1n.
  have hg1k : norm_class_higher NY NZ eq QN B g (1+k)%N by rewrite add1n.
  have hFk := @norm_class_higher_derivative_field R 1%N k X Y NX NY hNX hNY
    P ep PN hP PF epF PNF hPF A f F hf1k hF.
  have hGk := @norm_class_higher_derivative_field R 1%N k Y Z NY NZ hNY hNZ
    Q eq QN hQ QF eqF QNF hQF B g G hg1k hG.
  have hFC := norm_class_higher_open_restriction hNX hPN hPF hCA hopen hFk.
  have hGC := ih Y (Q 1%N) NY (@QN 1%N) hNY hQN
    P QF T ep PN eqF QNF et TN hP hQF hT A B f G hfprev hGk.
  pose opP := @continuous_multilinear_one_evaluation R X Y (P 1%N) NX NY
    (@ep 1%N) (@PN 1%N) (@hP 1%N).
  pose opQ := @continuous_multilinear_one_evaluation R Y Z (Q 1%N) NY NZ
    (@eq 1%N) (@QN 1%N) (@hQ 1%N).
  pose opS := @continuous_multilinear_one_evaluation R X Z (S 1%N) NX NZ
    (@es 1%N) (@SN 1%N) (@hS 1%N).
  have hopP := continuous_multilinear_one_operator_space (@hP 1%N).
  have hopQ := continuous_multilinear_one_operator_space (@hQ 1%N).
  have hopS := continuous_multilinear_one_operator_space (@hS 1%N).
  have [Comp [hComp hCompE]] := continuous_operator_composition_exists hopP hopQ hopS.
  pose H x := Comp (F x) (G (f x)).
  have hHC : norm_class_higher NX (@SN 1%N) esF SNF C H k.
    exact: (@norm_class_higher_bilinear R X NX hNX k
      (P 1%N) (Q 1%N) (S 1%N) (@PN 1%N) (@QN 1%N) (@SN 1%N)
      hPN hQN hSN PF T SF epF PNF et TN esF SNF hPF hT hSF
      C F (fun x=>G (f x)) Comp hComp hFC hGC).
  have hH a (ha : C a) :
      has_norm_higher_differential NX es SN C (fun x=>g (f x)) 1%N a (H a).
    apply: (@norm_higher_differential_first R X Z NX NZ hNX hNZ S es SN hS
      C (fun x=>g (f x)) a (H a)).2.
    change (has_norm_differential NX NZ C (fun x=>g (f x)) a
      (opS (Comp (F a) (G (f a))))).
    rewrite hCompE.
    exact (norm_differential_chain hNX hNY hNZ
      ((@norm_higher_differential_first R X Y NX NY hNX hNY
        P ep PN hP A f a (F a)).1 (hF a ha.1))
      ((@norm_higher_differential_first R Y Z NY NZ hNY hNZ
        Q eq QN hQ B g (f a) (G (f a))).1 (hG (f a) ha.2))).
  have hresult := @norm_class_higher_from_derivative_field R 1%N k X Z
    NX NZ hNX hNZ S es SN hS SF esF SNF hSF
    C (fun x=>g (f x)) H hzero hH hHC.
  by rewrite add1n in hresult.
Qed.
End HigherComposition.
