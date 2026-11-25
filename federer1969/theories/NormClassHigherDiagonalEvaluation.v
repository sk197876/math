(** Federer (1969), 3.1.11, pp. 220–221:
    diagonal evaluation of a continuous multilinear
    form field preserves differentiability class.
    Repeated last-vector contraction reduces the
    assertion to bounded bilinear operations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearSealed
  ContinuousMultilinearEvaluationBound ContinuousMultilinearSuccessorContraction
  MultilinearSuccessorArguments NormClassHigherUP NormClassHigherBilinear
  NormClassHigherPostcompose NormClassHigherLocalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DiagonalRegularity.
Variable R : realType.
Variables T X Y : lmodType R.
Variables (NT : T->R) (NX : X->R) (NY : Y->R).
Hypothesis hNT : is_real_norm NT.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ez : forall n, {ffun 'I_n->X}->Hom (Z n) Y.
Variable ZN : forall n, Z n->R.
Hypothesis hZ : forall n, is_continuous_multilinear_space NX NY (@ez n) (@ZN n).
Variables P S : nat->lmodType R.
Variable ep : forall j, {ffun 'I_j->T}->Hom (P j) X.
Variable PN : forall j, P j->R.
Variable es : forall j, {ffun 'I_j->T}->Hom (S j) Y.
Variable SN : forall j, S j->R.
Hypothesis hP : forall j, is_continuous_multilinear_space NT NX (@ep j) (@PN j).
Hypothesis hS : forall j, is_continuous_multilinear_space NT NY (@es j) (@SN j).
Variable U : T->Prop.

(** Source for [norm_class_higher_diagonal_evaluation]:
    continuous polynomial evaluation is built from
    continuous bilinear contractions, supporting the
    polynomial smoothness assertion in Federer 3.1.11,
    p. 221. Both the form and
    its repeated argument may vary with the
    parameter, and degree zero is included. *)
Theorem norm_class_higher_diagonal_evaluation k n :
  forall (W : nat->lmodType R)
    (ew : forall j, {ffun 'I_j->T}->Hom (W j) (Z n))
    (WN : forall j, W j->R)
    (hW : forall j, is_continuous_multilinear_space NT (@ZN n) (@ew j) (@WN j))
    (D : T->Z n) (v : T->X),
  norm_class_higher NT (@ZN n) ew WN U D k ->
  norm_class_higher NT NX ep PN U v k ->
  norm_class_higher NT NY es SN U
    (fun t=>@ez n [ffun _ : 'I_n=>v t] (D t)) k.
Proof.
elim: n=>[|n ih] W ew WN hW D v hcD hcv.
- pose u0 := [ffun _ : 'I_0=>(0 : X)].
  have hb := continuous_multilinear_evaluation_bounded hNX (@hZ 0%N) u0.
  have hc := @norm_class_higher_postcompose R T (Z 0%N) Y NT (@ZN 0%N) NY
    hNT (continuous_multilinear_norm_is_norm hNY (@hZ 0%N)) hNY
    W S ew WN es SN hW hS U D (@ez 0%N u0) k hb hcD.
  apply: (@norm_class_higher_domain_agreement R T Y NT NY hNT hNY
    S es SN hS U (fun t=>@ez 0%N u0 (D t))
    (fun t=>@ez 0%N [ffun _ : 'I_0=>v t] (D t)) k _ hc).
  move=>t _; congr (@ez 0%N _ (D t)); apply/ffunP=>i; by case: i.
- have hNn := continuous_multilinear_norm_is_norm hNY (@hZ n).
  have hNn1 := continuous_multilinear_norm_is_norm hNY (@hZ n.+1).
  pose V j := @ContinuousMultilinear.space R j T (Z n) NT (@ZN n) hNT hNn.
  pose ev j := @ContinuousMultilinear.evaluation R j T (Z n) NT (@ZN n) hNT hNn.
  pose VN j := @ContinuousMultilinear.norm R j T (Z n) NT (@ZN n) hNT hNn.
  have hV j : is_continuous_multilinear_space NT (@ZN n) (ev j) (VN j).
    exact: ContinuousMultilinear.laws.
  have [C [hC hCE]] :=
    continuous_multilinear_successor_contraction_exists hNX (@hZ n) (@hZ n.+1).
  have hc := @norm_class_higher_bilinear R T NT hNT k
    (Z n.+1) X (Z n) (@ZN n.+1) NX (@ZN n) hNn1 hNX hNn
    W P V ew WN ep PN ev VN hW hP hV U D v C hC hcD hcv.
  have hh := ih V ev VN hV (fun t=>C (D t) (v t)) v hc hcv.
  apply: (@norm_class_higher_domain_agreement R T Y NT NY hNT hNY
    S es SN hS U
    (fun t=>@ez n [ffun _ : 'I_n=>v t] (C (D t) (v t)))
    (fun t=>@ez n.+1 [ffun _ : 'I_n.+1=>v t] (D t)) k _ hh).
  by move=>t _; rewrite hCE multilinear_successor_constant_arguments.
Qed.
End DiagonalRegularity.
