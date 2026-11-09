(** Federer (1969), 3.4.5, p. 320: every
    finitely generated ideal determines a unique analytic variety
    germ satisfying all original generator equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing SetGermUP
  CommutativeIdealUP FiniteZeroSetSealed FiniteGermZeroSystem FiniteGermGenerators
  FiniteGeneratedGermVariety IdealVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ideal_variety_germ_exists]: existence of
    var(I) with the original all-generator characterization,
    3.4.5, p. 320. A chosen finite system
    proves existence; independence removes its choice from
    every exposed property. *)
Theorem ideal_variety_germ_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  is_finitely_generated_commutative_ideal I ->exists alpha,
    @is_ideal_variety_germ R X NX hNX a I alpha.
Proof.
move=>hFinite.
have [J [f [U [ha [hU [hAnalytic hGenerated]]]]]]:=
  @finite_germ_generator_system_exists R X NX hNX a I hFinite.
pose alpha:=@set_germ (Topological.clone (real_norm_metric_space hNX) _) a
  (@FiniteZeroSet.value [the zmodType of R^o] X U J (fun j=>analytic_representative_value (f j))).
exists alpha;constructor.
- exact:(@finite_germ_zero_system_variety R X NX hNX a J f U ha hU hAnalytic).
- move=>K g V haV hV hGAnalytic hGGenerated.
  exact:(@finite_generated_germ_variety_independent R X NX hNX a J K f g U V I
    ha hU haV hV hGenerated hGGenerated).
Qed.

(** Source for [ideal_variety_germ_unique]: the all-system
    law determines one original variety germ, 3.4.5, p. 320. *)
Lemma ideal_variety_germ_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) alpha beta:
  is_finitely_generated_commutative_ideal I ->
  @is_ideal_variety_germ R X NX hNX a I alpha ->
  @is_ideal_variety_germ R X NX hNX a I beta ->alpha=beta.
Proof.
move=>hFinite hAlpha hBeta.
have [J [f [U [ha [hU [hAnalytic hGenerated]]]]]]:=
  @finite_germ_generator_system_exists R X NX hNX a I hFinite.
by rewrite (@ideal_variety_germ_original_equation R X NX hNX a I alpha hAlpha J f U ha hU hAnalytic hGenerated)
  (@ideal_variety_germ_original_equation R X NX hNX a I beta hBeta J f U ha hU hAnalytic hGenerated).
Qed.
