(** Federer (1969), 3.4.5, pp. 318–321: finite
    sums retain actual finite jet agreement, supporting the
    original finite coefficient remainders. This uses the
    linear higher differential laws of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialFiniteSums NormAnalyticUP
  NormAnalyticHigherJet NormFiniteJetAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Sums.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Local Notation AN A f:=(@norm_analytic R X Y NX NY hNX hNY A f).

(** Source for [norm_finite_jet_finite_sum_agreement]: finite
    sums of actual agreeing jets agree at the original
    centre in every retained order, supporting 3.4.5,
    pp. 318–321. The original open domain is
    explicit, including the empty index family. *)
Theorem norm_finite_jet_finite_sum_agreement (A:set X) (I:finType)
    (f g:I->X->Y) k a:
  A a ->(forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,AN A (f i)) ->(forall i,AN A (g i)) ->
  (forall i,norm_finite_jet_agreement NX ev NZ A A (f i) (g i) k a) ->
  norm_finite_jet_agreement NX ev NZ A A (fun x=>\sum_i f i x) (fun x=>\sum_i g i x) k a.
Proof.
move=>ha hOpen hf hg hAgree m hm z.
have hexF i:exists D:X->Z m,forall x,A x ->has_norm_higher_differential NX ev NZ A (f i) m x (D x).
  have [D [hD hAnalyticD]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY m A (f i) (hf i).
  by exists D.
have hexG i:exists D:X->Z m,forall x,A x ->has_norm_higher_differential NX ev NZ A (g i) m x (D x).
  have [D [hD hAnalyticD]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY m A (g i) (hg i).
  by exists D.
have [D hD]:=choice hexF.
have [E hE]:=choice hexG.
have hSumD:=@norm_higher_differential_finite_sum R X Y NX NY hNX hNY Z ev NZ hZ A hOpen I f m D hD.
have hSumE:=@norm_higher_differential_finite_sum R X Y NX NY hNX hNY Z ev NZ hZ A hOpen I g m E hE.
have hPoint i:D i a=E i a.
  have hGActual:has_norm_higher_differential NX ev NZ A (g i) m a (D i a):=
    (hAgree i m hm (D i a)).1 (hD i a ha).
  exact:(norm_higher_differential_unique hNX hNY hZ hGActual (hE i a ha)).
have hSumPoint:(\sum_i D i a)=\sum_i E i a by apply:eq_bigr=>i _;exact:hPoint.
have hGSum:has_norm_higher_differential NX ev NZ A (fun x=>\sum_i g i x) m a (\sum_i D i a).
  rewrite hSumPoint;exact:hSumE a ha.
split=>hz.
- have hEqual:z=\sum_i D i a:=norm_higher_differential_unique hNX hNY hZ hz (hSumD a ha).
  by rewrite hEqual.
- have hEqual:z=\sum_i D i a:=norm_higher_differential_unique hNX hNY hZ hz hGSum.
  rewrite hEqual;exact:hSumD a ha.
Qed.
End Sums.
