(** Federer (1969), 3.4.8(16), p. 337:
    var(ideal sigma) is the smallest analytic variety
    germ containing sigma. This is a consequence of
    the already proved ideal recovery and separation laws
    of 3.4.5, p. 320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRing SetGermUP SetGermOrder
  CommutativeIdealUP GermVanishingSealed GermVanishingMonotonicity AnalyticVarietyGermUP
  AnalyticVarietyGermSeparation IdealVarietyGermSealed IdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_hull_minimality]: the original minimality
    assertion in the first sentence of the proof
    of 3.4.8(16), p. 337. The source
    germ need not itself be analytic or measurable. *)
Theorem analytic_hull_minimality (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (sigma beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (hI:@is_finitely_generated_commutative_ideal [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]
      (@AnalyticSetIdeal.value R X NX hNX a sigma)):
  @is_analytic_variety_germ R X NX hNX a beta ->set_germ_subset sigma beta ->
  set_germ_subset (@IdealVarietyGerm.value R X NX hNX a _ hI) beta.
Proof.
move=>hBeta hSub.
apply:(@analytic_variety_germ_ideal_separation R X NX hNX a beta _ hBeta).
rewrite (@vanishing_ideal_variety_recovery R X NX hNX a sigma hI).
exact:(@analytic_set_ideal_antitone R X NX hNX a sigma beta hSub).
Qed.
