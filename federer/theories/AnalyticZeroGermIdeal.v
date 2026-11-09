(** Federer (1969), 3.4.5, p. 320: membership
    in the ideal of a set germ is exactly containment
    in the original zero variety germ of the function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws
  SetGermUP SetGermLaws SetGermOrder GermVanishingUP GermVanishingSealed GermVanishingRepresentative
  AnalyticZeroGermUP AnalyticZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_germ_ideal_equivalence]: the
    original local-vanishing definition is equivalent to set
    germ containment, supporting irreducibility in 3.4.5, p. 320. *)
Theorem analytic_zero_germ_ideal_equivalence (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (alpha:analytic_germ_space hNX a):
  @AnalyticSetIdeal.value R X NX hNX a sigma alpha <->
  set_germ_subset sigma (@AnalyticZeroGerm.value R X NX hNX a alpha).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [S <-]:=@set_germ_has_representative T a sigma.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite -hf (analytic_set_ideal_representative_equation f S)
  -(@AnalyticZeroGerm.laws R X NX hNX a (analytic_germ f) f (erefl _))
  set_germ_subset_original.
by [].
Qed.
