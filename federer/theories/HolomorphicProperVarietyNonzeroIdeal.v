(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 333:
    a proper holomorphic variety germ has
    a nonzero vanishing ideal. Apply the
    original ideal-separation theorem from 3.4.5;
    no later dimension theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicGermOperationsUP ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing SetGermUP
  SetGermSealed SetGermLaws SetGermOrder CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  HolomorphicVarietyGermUP HolomorphicVarietyGermSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_proper_variety_nonzero_ideal]:
    the actual critical variety has a
    nonzero ideal unless its germ is
    the whole germ, supporting the dimension
    drop in 3.4.12, p. 339, extending 3.4.8(11), p. 333. *)
Theorem holomorphic_proper_variety_nonzero_ideal (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) a setT ->
  exists beta,@HolomorphicSetIdeal.value R X NX hNX a alpha beta /\ beta<>@holomorphic_germ_zero R X NX hNX a.
Proof.
move=>hAlpha hProper.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
pose I:=@HolomorphicSetIdeal.value R X NX hNX a.
apply:contrapT=>hNo;apply:hProper.
have hZero:forall beta:G,I alpha beta ->beta = 0.
  move=>beta hBeta;apply:contrapT=>hNonzero;apply:hNo;by exists beta.
have hInclusion:I alpha `<=` I (@set_germ T a setT).
  move=>beta hBeta;rewrite (hZero beta hBeta).
  exact:commutative_ideal_zero (holomorphic_set_ideal_ring_laws _).
have hWholeSub:=@holomorphic_variety_germ_ideal_separation R X NX hNX a alpha
  (@set_germ T a setT) hAlpha hInclusion.
apply:set_germ_subset_antisymmetric;last exact:hWholeSub.
rewrite /set_germ_subset set_germ_intersection_whole.
reflexivity.
Qed.
