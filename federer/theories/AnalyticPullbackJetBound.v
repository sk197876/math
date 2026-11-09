(** Federer (1969), 3.4.5, p. 319: a fixed actual
    analytic map gives finite derivative control of its germ
    pullback in every order, including the original value at order zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRingLaws AnalyticGermGrowthUP AnalyticGermZerothNorm
  AnalyticPullbackRepresentative AnalyticPullbackUP AnalyticPullbackSealed AnalyticPullbackPositiveJetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_pullback_jet_bound]: all
    orders of the actual pullback homomorphism in 3.4.5,
    p. 319. The bound is derived from the actual map;
    no derivative estimate is an extra theorem hypothesis. *)
Theorem analytic_germ_pullback_jet_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (u:X->Y) a
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a) m:
  exists K:R,0<=K /\forall (alpha:analytic_germ_space hNY (u a)) (B:R),
    0<=B ->(forall i,(i<=m)%N ->@analytic_germ_jet_norm R Y NY hNY (u a) i alpha<=B) ->
    @analytic_germ_jet_norm R X NX hNX a m
      (@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu alpha)<=K*B.
Proof.
case:m=>[|m].
- exists 1;split;first exact:ler01.
  move=>alpha B hB hAlpha.
  have [f hf]:=@analytic_germ_has_representative R Y NY hNY (u a) alpha.
  pose g:=@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f.
  have hg:analytic_germ g=@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu alpha.
    by rewrite -hf (@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu).
  rewrite (analytic_germ_zeroth_norm hg) mul1r.
  have hEstimate:=hAlpha 0%N (leqnn 0%N).
  by rewrite (analytic_germ_zeroth_norm hf) in hEstimate.
- apply:analytic_germ_pullback_positive_jet_bound;by [].
Qed.
