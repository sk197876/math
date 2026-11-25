(** Federer (1969), 3.4.5, p. 320: analytic
    variety germs are exactly the zero germs of individual
    analytic equations, by the original sum-of-squares reduction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP AnalyticGermUP AnalyticGermRingLaws AnalyticGermNeighbourhood AnalyticGermRepresentatives
  SetGermUP SetGermLocality FiniteAnalyticVarietyUP FiniteAnalyticVarietyLaws
  AnalyticVarietyGermUP AnalyticZeroGermUP AnalyticZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Varieties.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation zero:=(@AnalyticZeroGerm.value R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).

(** Source for [analytic_zero_germ_is_variety]: the
    zero germ of one actual analytic function belongs to
    V_a(X), 3.4.5, p. 320. *)
Lemma analytic_zero_germ_is_variety (alpha:AnalyticGermUP.analytic_germ_space hNX a):
  @is_analytic_variety_germ R X NX hNX a (zero alpha).
Proof.
have [f hf]:=@AnalyticGermRingLaws.analytic_germ_has_representative R X NX hNX a alpha.
have [U [ha [hUT [hU hAnalytic]]]]:=analytic_germ_open_representative (analytic_representative_analytic f).
pose S:set X:=U `&` [set x|analytic_representative_value f x=0].
exists U,S;split;first exact:ha.
split.
- split;first exact:hU.
  exists (Finite.clone 'I_1 _),(fun _=>analytic_representative_value f);split;first by move=>_.
  move=>x;split.
  + move=>[hx hZero];split;first exact:hx.
    by move=>_.
  + move=>[hx hZero];split;first exact:hx.
    exact:hZero ord0.
- rewrite /S (@set_germ_neighbourhood_intersection T a U [set x|analytic_representative_value f x=0] hU ha).
  exact:(@AnalyticZeroGerm.laws R X NX hNX a alpha f hf).
Qed.

(** Source for [analytic_variety_germ_single_equation]:
    every original analytic variety germ is a one-equation
    zero germ, by the sum-of-squares statement in 3.4.5, p. 320. *)
Theorem analytic_variety_germ_single_equation
    (sigma:@set_germ_space T a):
  @is_analytic_variety_germ R X NX hNX a sigma ->
  exists alpha:AnalyticGermUP.analytic_germ_space hNX a,zero alpha=sigma.
Proof.
move=>[U [S [ha [hVar hGerm]]]].
have [h [hAnalytic hSet]]:=@finite_analytic_variety_one_equation R X NX hNX U S hVar.
have [f hf]:=@analytic_representative_from_domain R X NX hNX a U h (hAnalytic a ha).
exists (AnalyticGermUP.analytic_germ f).
rewrite -(@AnalyticZeroGerm.laws R X NX hNX a _ f (erefl _)).
have hEquality:S=U `&` [set x|analytic_representative_value f x=0].
  apply/seteqP;split=>x;by rewrite hf (hSet x).
have hLocal:sgerm S=sgerm [set x|analytic_representative_value f x=0].
  rewrite hEquality;exact:(@set_germ_neighbourhood_intersection T a U [set x|analytic_representative_value f x=0] hVar.1 ha).
by rewrite -hLocal.
Qed.
End Varieties.
