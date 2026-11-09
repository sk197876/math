(** Federer (1969), 3.4.5, p. 320: finite
    analytic equations separate variety germs, so their
    vanishing ideals determine their original local sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP
  SetGermUP SetGermLaws SetGermOrder GermVanishingSealed GermVanishingMonotonicity
  FiniteZeroSetSealed FiniteGermZeroSystem FiniteGermVanishingContainment
  AnalyticVarietyGermUP AnalyticVarietyGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_variety_germ_ideal_separation]:
    among actual analytic variety germs, ideal inclusion
    reverses set-germ inclusion, supporting irreducibility
    and components in 3.4.5, pp. 320–321. *)
Theorem analytic_variety_germ_ideal_separation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_analytic_variety_germ R X NX hNX a alpha ->
  @AnalyticSetIdeal.value R X NX hNX a alpha `<=` @AnalyticSetIdeal.value R X NX hNX a beta ->
  set_germ_subset beta alpha.
Proof.
move=>hAlpha hIdeal.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [J [f [U [ha [hU [hAnalytic hAlphaEquation]]]]]]:=
  @analytic_variety_germ_equation_system R X NX hNX a alpha hAlpha.
have [S hS]:=@set_germ_has_representative T a beta.
rewrite -hS -hAlphaEquation.
apply:(@finite_germ_vanishing_containment R X NX hNX a J f U S ha hU)=>j.
have hGenerator:=@finite_germ_zero_system_generators_vanish R X NX hNX a J f U ha hU j.
rewrite hAlphaEquation in hGenerator.
have hBeta:=hIdeal _ hGenerator.
by rewrite hS.
Qed.

(** Source for [analytic_variety_germ_ideal_injective]:
    actual analytic variety germs with equal ideals are
    equal, supporting the original recovery and component
    assertions of 3.4.5, pp. 320–321. *)
Lemma analytic_variety_germ_ideal_injective (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_analytic_variety_germ R X NX hNX a alpha ->
  @is_analytic_variety_germ R X NX hNX a beta ->
  @AnalyticSetIdeal.value R X NX hNX a alpha=@AnalyticSetIdeal.value R X NX hNX a beta ->alpha=beta.
Proof.
move=>hAlpha hBeta hEqual;apply:set_germ_subset_antisymmetric.
- apply:(@analytic_variety_germ_ideal_separation R X NX hNX a beta alpha hBeta).
  by rewrite hEqual.
- apply:(@analytic_variety_germ_ideal_separation R X NX hNX a alpha beta hAlpha).
  by rewrite hEqual.
Qed.
