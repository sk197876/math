(** Federer (1969), 3.4.5, pp. 318–321: actual
    iterated divided Taylor coefficient fields, supporting
    the two-coordinate remainder proof of the cited example.
    Representatives remain local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP NormFiniteJetAgreement AnalyticDirectionalCoefficient AnalyticDirectionalCoefficientAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Iterated.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation AN A f:=(@norm_analytic R X Y NX NY hNX hNY A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).

(** Source for [analytic_iterated_directional_coefficients_exist]:
    actual analytic divided coefficient fields exist in both
    fixed original directions, supporting the coefficient argument
    of 3.4.5, pp. 318–321. All orders and
    their original derivative equations are retained. *)
Theorem analytic_iterated_directional_coefficients_exist (A:set X) (f:X->Y) v w:
  AN A f ->exists C:nat->X->Y,exists P:nat->nat->X->Y,
    (forall i,Coefficient A f i v (C i) /\AN A (C i)) /\
    forall i j,Coefficient A (C i) j w (P i j) /\AN A (P i j).
Proof.
move=>hf.
have hex i:exists c:X->Y,Coefficient A f i v c /\AN A c.
  exact:(@analytic_directional_coefficient_exists R X Y NX NY hNX hNY A f i v hf).
have [C hC]:=choice hex.
have hexP i:exists P:nat->X->Y,forall j,Coefficient A (C i) j w (P j) /\AN A (P j).
  have hEach j:exists c:X->Y,Coefficient A (C i) j w c /\AN A c.
    exact:(@analytic_directional_coefficient_exists R X Y NX NY hNX hNY A (C i) j w (hC i).2).
  have [P hP]:=choice hEach;by exists P.
have [P hP]:=choice hexP.
by exists C,P.
Qed.

(** Source for [analytic_iterated_directional_finite_jet_agreement]:
    taking i coefficients in the first direction and
    j in the second retains k original agreeing
    jets from order i+(j+k). This is actual iterated
    differentiation, supporting 3.4.5, pp. 318–321. *)
Theorem analytic_iterated_directional_finite_jet_agreement (A B:set X) (f g:X->Y)
    i j k a v w (C D P Q:X->Y):
  A a ->B a ->AN A f ->AN B g ->
  Coefficient A f i v C ->Coefficient B g i v D ->
  Coefficient A C j w P ->Coefficient B D j w Q ->
  norm_finite_jet_agreement NX ev NZ A B f g (i+(j+k))%N a ->
  norm_finite_jet_agreement NX ev NZ A B P Q k a.
Proof.
move=>ha hb hf hg hC hD hP hQ hAgree.
have hFirst:=@analytic_directional_coefficient_finite_jet_agreement R X Y NX NY hNX hNY
  A B f g i (j+k)%N a v C D ha hb hf hg hC hD hAgree.
have hAnalyticC:=@analytic_directional_coefficient_analytic R X Y NX NY hNX hNY A f i v C hf hC.
have hAnalyticD:=@analytic_directional_coefficient_analytic R X Y NX NY hNX hNY B g i v D hg hD.
exact:(@analytic_directional_coefficient_finite_jet_agreement R X Y NX NY hNX hNY
  A B C D j k a w P Q ha hb hAnalyticC hAnalyticD hP hQ hFirst).
Qed.
End Iterated.
