(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    pointed analytic coordinate pullbacks are continuous for
    the original germ metric. Uniqueness transfers the proved
    analytic composition theorem to the independent pointed laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermMetric AnalyticPullbackSealed AnalyticPullbackRepresentative
  AnalyticPullbackContinuity PointedAnalyticPullbackUP PointedAnalyticPullbackUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointed_analytic_germ_pullback_continuous]: the
    actual coordinate maps induce continuous maps of germs,
    supporting the original closed subrings and Borel
    assertions of 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_analytic_germ_pullback_continuous (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (u:X->Y) (a:X) (b:Y)
    (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  @norm_analytic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  is_pointed_analytic_germ_pullback u P ->
  continuous (fun alpha:@analytic_germ_metric R Y NY hNY b=>
    (P alpha:@analytic_germ_metric R X NX hNX a)).
Proof.
move=>hu hab hP;subst b.
pose Q:=@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu.
have hQ:is_pointed_analytic_germ_pullback u Q.
  move=>f;exists (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
  split;first exact:(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu f).
  by move=>x.
have hEqual:P=Q.
  apply:funext=>alpha.
  exact:(@pointed_analytic_germ_pullback_unique R X Y NX NY hNX hNY a (u a) u P Q hP hQ alpha).
rewrite hEqual.
exact:(@analytic_germ_pullback_continuous R X Y NX NY hNX hNY A u a hu).
Qed.
