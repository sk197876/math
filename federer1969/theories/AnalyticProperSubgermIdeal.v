(** Federer (1969), 3.4.8(11), p. 334:
    a proper analytic subgerm has a strictly
    larger vanishing ideal. Apply the existing
    ideal separation theorem of 3.4.5; no
    dimension or stratification theorem is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRing SetGermUP SetGermOrder
  AnalyticVarietyGermUP GermVanishingSealed GermVanishingMonotonicity AnalyticVarietyGermSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_proper_subgerm_ideal_witness]:
    the strict ideal inclusion for alpha
    intersect beta in 3.4.8(11), p. 334. *)
Theorem analytic_proper_subgerm_ideal_witness (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_analytic_variety_germ R X NX hNX a beta ->
  set_germ_subset beta alpha ->alpha<>beta ->
  exists f:@analytic_germ_ring R X NX hNX a,
    @AnalyticSetIdeal.value R X NX hNX a beta f /\
    ~@AnalyticSetIdeal.value R X NX hNX a alpha f.
Proof.
move=>hBeta hSub hDifferent.
apply:contrapT=>hNoWitness.
have hIdeal:@AnalyticSetIdeal.value R X NX hNX a beta `<=`
    @AnalyticSetIdeal.value R X NX hNX a alpha.
  move=>f hf;apply:contrapT=>hNot;apply:hNoWitness;by exists f.
have hReverse:=@analytic_variety_germ_ideal_separation R X NX hNX a beta alpha hBeta hIdeal.
apply:hDifferent;exact:set_germ_subset_antisymmetric hReverse hSub.
Qed.
