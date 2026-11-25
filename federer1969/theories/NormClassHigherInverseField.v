(** Federer (1969), 3.1.11, p. 220:
    pointwise inversion preserves class k for a
    field of invertible elements on a given open
    domain. This supporting form does not require
    the normed algebra to be complete. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom AlgebraUP RealNormUP AlgebraInverseUP
  NormDifferentialUP NormDifferentialInverseField NormAlgebraInverseDifferential
  NormClassOneUP NormClassZeroInverseField ContinuousOperatorUP
  ContinuousOperatorComposition ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearOne ContinuousMultilinearSealed AlgebraSandwichOperator
  NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherUP
  NormClassHigherLaws NormClassHigherArithmetic NormClassHigherDerivative
  NormClassHigherFromDerivative NormClassHigherBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section InverseFields.
Variable R : realType.
Variable X : lmodType R.
Variable A : algebra R.
Variables (NX : X->R) (N : A->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hN : is_real_norm N.
Hypothesis hM : forall x y, N (alg_mul A x y)<=N x*N y.
Variable Z : nat->lmodType R.
Variable ez : forall k, {ffun 'I_k->X}->Hom (Z k) A.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX N (@ez k) (@ZN k).
Variable U : X->Prop.
Variables P Q : X->A.
Hypothesis hInv : forall x, U x -> is_two_sided_algebra_inverse (P x) (Q x).

(** Source for [norm_class_higher_inverse_field]:
    the inverse-field step supporting the assertion
    about inverses of class-k maps in Federer
    3.1.11, p. 220. The first
    inverse differential is proved directly on U,
    then higher regularity follows by induction
    using bounded bilinear sandwich and composition maps.
    Completeness and any openness of the full
    algebra-inverse domain are unnecessary. *)
Theorem norm_class_higher_inverse_field k :
  norm_class_higher NX N ez ZN U P k ->
  norm_class_higher NX N ez ZN U Q k.
Proof.
elim: k=>[|k ih] hcP.
- apply: (@norm_class_higher_zero R X A NX N hN Z ez ZN hZ U Q).2.
  exact (norm_class_zero_inverse_field hN hM hInv hcP.1).
- have hzero := norm_class_zero_inverse_field hN hM hInv hcP.1.
  have hQk := ih (norm_class_higher_previous hNX hN hZ hcP).
  have h1 : (1<=k.+1)%N by [].
  have [_ [D [hD hcD]]] := @norm_class_higher_lower R X A NX N
    hNX hN Z ez ZN hZ U P k.+1 1%N h1 hcP.
  have hZN := continuous_multilinear_norm_is_norm hN (@hZ 1%N).
  pose W j := @ContinuousMultilinear.space R j X (Z 1%N) NX (@ZN 1%N) hNX hZN.
  pose ew j := @ContinuousMultilinear.evaluation R j X (Z 1%N) NX (@ZN 1%N) hNX hZN.
  pose WN j := @ContinuousMultilinear.norm R j X (Z 1%N) NX (@ZN 1%N) hNX hZN.
  have hW j : is_continuous_multilinear_space NX (@ZN 1%N) (ew j) (WN j).
    exact: ContinuousMultilinear.laws.
  have hP1k : norm_class_higher NX N ez ZN U P (1+k)%N by rewrite add1n.
  have hDk := @norm_class_higher_derivative_field R 1%N k X A NX N hNX hN
    Z ez ZN hZ W ew WN hW U P D hP1k hD.
  pose S := @ContinuousMultilinear.space R 1%N A A N N hN hN.
  pose es := @ContinuousMultilinear.evaluation R 1%N A A N N hN hN.
  pose SN := @ContinuousMultilinear.norm R 1%N A A N N hN hN.
  have hS : is_continuous_multilinear_space N N es SN := @ContinuousMultilinear.laws R 1%N A A N N hN hN.
  have hSN := continuous_multilinear_norm_is_norm hN hS.
  pose T j := @ContinuousMultilinear.space R j X S NX SN hNX hSN.
  pose et j := @ContinuousMultilinear.evaluation R j X S NX SN hNX hSN.
  pose TN j := @ContinuousMultilinear.norm R j X S NX SN hNX hSN.
  have hT j : is_continuous_multilinear_space NX SN (et j) (TN j).
    exact: ContinuousMultilinear.laws.
  have [B [hB hBE]] := algebra_sandwich_operator_exists hN hM hS.
  have hBk := @norm_class_higher_bilinear R X NX hNX k A A S N N SN
    hN hN hSN Z Z T ez ZN ez ZN et TN hZ hZ hT
    U Q Q B hB hQk hQk.
  pose OpZ := @continuous_multilinear_one_evaluation R X A (Z 1%N) NX N
    (@ez 1%N) (@ZN 1%N) (@hZ 1%N).
  pose OpS := @continuous_multilinear_one_evaluation R A A S N N es SN hS.
  have hopZ := continuous_multilinear_one_operator_space (@hZ 1%N).
  have hopS := continuous_multilinear_one_operator_space hS.
  have [Comp [hComp hCompE]] := continuous_operator_composition_exists hopZ hopS hopZ.
  pose F x := (-1 : R)*:Comp (D x) (B (Q x) (Q x)).
  have hCompk := @norm_class_higher_bilinear R X NX hNX k
    (Z 1%N) S (Z 1%N) (@ZN 1%N) SN (@ZN 1%N) hZN hSN hZN
    W T W ew WN et TN ew WN hW hT hW
    U D (fun x=>B (Q x) (Q x)) Comp hComp hDk hBk.
  have hFk : norm_class_higher NX (@ZN 1%N) ew WN U F k.
    exact: (@norm_class_higher_scale R X (Z 1%N) NX (@ZN 1%N)
      hNX hZN W ew WN hW U k
      (fun x=>Comp (D x) (B (Q x) (Q x))) (-1) hCompk).
  have hF a (ha : U a) :
      has_norm_higher_differential NX ez ZN U Q 1%N a (F a).
    have hdP := (@norm_higher_differential_first R X A NX N hNX hN Z ez ZN hZ U P a (D a)).1 (hD a ha).
    have hdQ := @norm_differential_inverse_field R X A NX N hNX hN hM
      U P Q a (OpZ (D a)) hInv hdP.
    apply: (@norm_higher_differential_first R X A NX N hNX hN Z ez ZN hZ U Q a (F a)).2.
    have he : OpZ (F a)=hom_comp (algebra_inverse_linear_term (Q a)) (OpZ (D a)).
      apply: hom_ext=>v.
      have hs : OpZ ((-1 : R)*:Comp (D a) (B (Q a) (Q a)))=
          (-1 : R)*:OpZ (Comp (D a) (B (Q a) (Q a))).
        exact: linearZ.
      rewrite /F hs hom_scaleE hCompE !hom_compE.
      change ((-1 : R)*:es [ffun _ : 'I_1=>OpZ (D a) v] (B (Q a) (Q a))=
        -alg_mul A (Q a) (alg_mul A (OpZ (D a) v) (Q a))).
      by rewrite hBE scaleNr scale1r.
    change (has_norm_differential NX N U Q a (OpZ (F a))).
    by rewrite he.
  have hh := @norm_class_higher_from_derivative_field R 1%N k X A NX N
    hNX hN Z ez ZN hZ W ew WN hW U Q F hzero hF hFk.
  by rewrite add1n in hh.
Qed.
End InverseFields.
