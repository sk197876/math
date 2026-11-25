(** Federer (1969), 3.4.8(10), p. 331:
    a positive delta-power equation for each
    ideal member recovers the original variety
    off delta's zero set. Apply the
    existing zero-product and finite-equation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing
  SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder SetGermDifferenceOrder
  CommutativeIdealUP GermVanishingSealed AnalyticZeroGermSealed AnalyticZeroGermLaws
  AnalyticZeroGermPowers AnalyticZeroGermIdeal IdealVarietyGermSealed
  IdealVarietyVanishingLaws IdealVarietyGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_saturation_variety_off_equation]:
    var(I_g) and var(F) have the same
    germ outside delta=0, as used for
    var(I_g)=var(J) union gamma_0(Z), 3.4.8(10), p. 331. *)
Theorem analytic_saturation_variety_off_equation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (I F:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I)
    (hF:is_finitely_generated_commutative_ideal F) delta:
  F `<=` I ->
  (forall alpha,I alpha ->exists u:nat,(0<u)%N /\F (delta^+u*alpha)) ->
  @SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) a
    (@IdealVarietyGerm.value R X NX hNX a I hI)
    (@SetGerms.neg (Topological.clone (real_norm_metric_space hNX) _) a
      (@AnalyticZeroGerm.value R X NX hNX a delta)) =
  @SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) a
    (@IdealVarietyGerm.value R X NX hNX a F hF)
    (@SetGerms.neg (Topological.clone (real_norm_metric_space hNX) _) a
      (@AnalyticZeroGerm.value R X NX hNX a delta)).
Proof.
move=>hFI hPower.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose varI:=@IdealVarietyGerm.value R X NX hNX a I hI.
pose varF:=@IdealVarietyGerm.value R X NX hNX a F hF.
pose zero:=@AnalyticZeroGerm.value R X NX hNX a.
pose off:=@SetGerms.meet T a varF (@SetGerms.neg T a (zero delta)).
apply:set_germ_subset_antisymmetric.
- apply:set_germ_subset_meet_bound.
  + apply:(set_germ_subset_transitive (set_germ_meet_subset_left _ _)).
    exact:(@ideal_variety_germ_antitone R X NX hNX a F I hF hI hFI).
  + exact:set_germ_meet_subset_right.
- apply:set_germ_subset_meet_bound;last exact:set_germ_meet_subset_right.
  apply:ideal_variety_germ_contains_vanishing_set=>alpha hAlpha.
  have [u [hU hMember]]:=hPower alpha hAlpha.
  have hVanish:=@ideal_in_vanishing_ideal_of_variety R X NX hNX a F hF _ hMember.
  have hContain:=(@analytic_zero_germ_ideal_equivalence R X NX hNX a varF _).1 hVanish.
  rewrite (@analytic_zero_germ_product R X NX hNX a)
    (@analytic_zero_germ_positive_power R X NX hNX a delta u hU) in hContain.
  apply:(@analytic_zero_germ_ideal_equivalence R X NX hNX a off alpha).2.
  exact:(@set_germ_difference_union_cancel T a varF (zero alpha) (zero delta) hContain).
Qed.
