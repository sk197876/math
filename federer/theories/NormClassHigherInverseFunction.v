(** Federer (1969), 3.1.11, p. 220:
    if f is of class k and has an
    inverse of class one, that inverse is
    of class k. The spaces are arbitrary
    normed spaces, exactly as in the statement. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialInverseIdentities NormClassOneUP ContinuousOperatorUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialFirst
  NormClassHigherUP NormClassHigherLaws NormClassHigherDerivative
  NormClassHigherFromDerivative NormClassHigherComposition
  NormClassHigherRestriction NormClassHigherOperatorInverseField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section InverseFunction.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variables P Q : nat->lmodType R.
Variable ep : forall j, {ffun 'I_j->X}->Hom (P j) Y.
Variable PN : forall j, P j->R.
Variable eq : forall j, {ffun 'I_j->Y}->Hom (Q j) X.
Variable QN : forall j, Q j->R.
Hypothesis hP : forall j, is_continuous_multilinear_space NX NY (@ep j) (@PN j).
Hypothesis hQ : forall j, is_continuous_multilinear_space NY NX (@eq j) (@QN j).
Variables (A : X->Prop) (B : Y->Prop).
Variables (f : X->Y) (g : Y->X).
Hypothesis hfmap : forall x, A x -> B (f x).
Hypothesis hgmap : forall y, B y -> A (g y).
Hypothesis hgf : forall x, A x -> g (f x)=x.
Hypothesis hfg : forall y, B y -> f (g y)=y.

(** Source for [norm_class_higher_inverse_function]:
    Federer 3.1.11, p. 220: the class-one
    inverse of a class-k map is class k.
    The proof differentiates the inverse identities
    and inducts on k. It uses only
    pointwise inversion of operator fields, so no
    completeness assumption is imposed on X or Y. *)
Theorem norm_class_higher_inverse_function k :
  norm_class_higher NX NY ep PN A f k ->
  norm_class_higher NY NX eq QN B g 1%N ->
  norm_class_higher NY NX eq QN B g k.
Proof.
elim: k=>[|k ih] hf hg.
- apply: (@norm_class_higher_zero R Y X NY NX hNX Q eq QN hQ B g).2; exact hg.1.
- have hgk := ih (norm_class_higher_previous hNX hNY hP hf) hg.
  have hle : (1<=k.+1)%N by [].
  have [_ [F [hF hcF]]] := @norm_class_higher_lower R X Y NX NY
    hNX hNY P ep PN hP A f k.+1 1%N hle hf.
  have [G [hG hcG]] := hg.2.
  have hPN := continuous_multilinear_norm_is_norm hNY (@hP 1%N).
  have hQN := continuous_multilinear_norm_is_norm hNX (@hQ 1%N).
  pose PF j := @ContinuousMultilinear.space R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose epF j := @ContinuousMultilinear.evaluation R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  pose PNF j := @ContinuousMultilinear.norm R j X (P 1%N) NX (@PN 1%N) hNX hPN.
  have hPF j : is_continuous_multilinear_space NX (@PN 1%N) (epF j) (PNF j).
    exact: ContinuousMultilinear.laws.
  pose T j := @ContinuousMultilinear.space R j Y (P 1%N) NY (@PN 1%N) hNY hPN.
  pose et j := @ContinuousMultilinear.evaluation R j Y (P 1%N) NY (@PN 1%N) hNY hPN.
  pose TN j := @ContinuousMultilinear.norm R j Y (P 1%N) NY (@PN 1%N) hNY hPN.
  have hT j : is_continuous_multilinear_space NY (@PN 1%N) (et j) (TN j).
    exact: ContinuousMultilinear.laws.
  pose QF j := @ContinuousMultilinear.space R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  pose eqF j := @ContinuousMultilinear.evaluation R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  pose QNF j := @ContinuousMultilinear.norm R j Y (Q 1%N) NY (@QN 1%N) hNY hQN.
  have hQF j : is_continuous_multilinear_space NY (@QN 1%N) (eqF j) (QNF j).
    exact: ContinuousMultilinear.laws.
  have hf1k : norm_class_higher NX NY ep PN A f (1+k)%N by rewrite add1n.
  have hFk := @norm_class_higher_derivative_field R 1%N k X Y NX NY
    hNX hNY P ep PN hP PF epF PNF hPF A f F hf1k hF.
  have hFG := @norm_class_higher_composition R Y NY hNY k X (P 1%N)
    NX (@PN 1%N) hNX hPN Q PF T eq QN epF PNF et TN hQ hPF hT
    B A g F hgk hFk.
  have hsub y (hy : B y) : B y /\ A (g y) := conj hy (@hgmap y hy).
  have hopen y (hy : B y) := (hg.1 y hy).1.
  have hFGk := @norm_class_higher_open_restriction R Y (P 1%N) NY (@PN 1%N)
    hNY hPN T et TN hT (fun y=>B y /\ A (g y)) B (fun y=>F (g y))
    k hsub hopen hFG.
  pose opP := @continuous_multilinear_one_evaluation R X Y (P 1%N) NX NY
    (@ep 1%N) (@PN 1%N) (@hP 1%N).
  pose opQ := @continuous_multilinear_one_evaluation R Y X (Q 1%N) NY NX
    (@eq 1%N) (@QN 1%N) (@hQ 1%N).
  have hopP := continuous_multilinear_one_operator_space (@hP 1%N).
  have hopQ := continuous_multilinear_one_operator_space (@hQ 1%N).
  have hInv y (hy : B y) :
      (forall x, opQ (G y) (opP (F (g y)) x)=x) /\
      (forall z, opP (F (g y)) (opQ (G y) z)=z).
    have hdF := (@norm_higher_differential_first R X Y NX NY hNX hNY P ep PN hP A f (g y) (F (g y))).1 (hF (g y) (@hgmap y hy)).
    have hdG := (@norm_higher_differential_first R Y X NY NX hNY hNX Q eq QN hQ B g y (G y)).1 (hG y hy).
    have hdGy : has_norm_differential NY NX B g (f (g y)) (opQ (G y)).
      by rewrite (@hfg y hy).
    have hleft := norm_differentials_left_inverse hNX hNY hfmap hgf hdF hdGy.
    have hright := norm_differentials_left_inverse hNY hNX hgmap hfg hdG hdF.
    split.
    - move=> x; have hh := congr1 (fun L : Hom X X=>L x) hleft.
      by rewrite hom_compE hom_of_linearE /= in hh.
    - move=> z; have hh := congr1 (fun L : Hom Y Y=>L z) hright.
      by rewrite hom_compE hom_of_linearE /= in hh.
  have hGk := @norm_class_higher_operator_inverse_field R Y X Y (P 1%N) (Q 1%N)
    NY NX NY hNY hNX hNY opP (@PN 1%N) opQ (@QN 1%N) hopP hopQ
    T QF et TN eqF QNF hT hQF B (fun y=>F (g y)) G k hInv hFGk.
  have hh := @norm_class_higher_from_derivative_field R 1%N k Y X NY NX
    hNY hNX Q eq QN hQ QF eqF QNF hQF B g G hg.1 hG hGk.
  by rewrite add1n in hh.
Qed.
End InverseFunction.
