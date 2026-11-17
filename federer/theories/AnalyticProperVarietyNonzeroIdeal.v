(** Federer (1969), 3.4.8(11), p. 333:
    a proper analytic variety germ has
    a nonzero vanishing ideal. Apply the
    original ideal-separation theorem from 3.4.5;
    no later dimension theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP
  SetGermSealed SetGermLaws SetGermOrder CommutativeIdealUP GermVanishingSealed GermVanishingIdeal
  AnalyticVarietyGermUP AnalyticVarietyGermSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_proper_variety_nonzero_ideal]:
    the actual critical variety has a
    nonzero ideal unless its germ is
    the whole germ, supporting the dimension
    drop in 3.4.8(11), p. 333. *)
Theorem analytic_proper_variety_nonzero_ideal (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_analytic_variety_germ R X NX hNX a alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) a setT ->
  exists beta,@AnalyticSetIdeal.value R X NX hNX a alpha beta /\ beta<>@analytic_germ_zero R X NX hNX a.
Proof.
move=>hAlpha hProper.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose I:=@AnalyticSetIdeal.value R X NX hNX a.
apply:contrapT=>hNo;apply:hProper.
have hZero:forall beta:G,I alpha beta ->beta = 0.
  move=>beta hBeta;apply:contrapT=>hNonzero;apply:hNo;by exists beta.
have hInclusion:I alpha `<=` I (@set_germ T a setT).
  move=>beta hBeta;rewrite (hZero beta hBeta).
  exact:commutative_ideal_zero (analytic_set_ideal_ring_laws _).
have hWholeSub:=@analytic_variety_germ_ideal_separation R X NX hNX a alpha
  (@set_germ T a setT) hAlpha hInclusion.
apply:set_germ_subset_antisymmetric;last exact:hWholeSub.
rewrite /set_germ_subset set_germ_intersection_whole.
reflexivity.
Qed.
