(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: finite
    analytic equations separate variety germs, so their
    vanishing ideals determine their original local sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP
  SetGermUP SetGermLaws SetGermOrder HolomorphicGermVanishingSealed HolomorphicGermVanishingMonotonicity
  FiniteZeroSetSealed FiniteHolomorphicGermZeroSystem FiniteHolomorphicGermVanishingContainment
  HolomorphicVarietyGermUP HolomorphicVarietyGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_variety_germ_ideal_separation]:
    among actual analytic variety germs, ideal inclusion
    reverses set-germ inclusion, supporting irreducibility
    and components in 3.4.5, pp. 320–321. *)
Theorem holomorphic_variety_germ_ideal_separation (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  @HolomorphicSetIdeal.value R X NX hNX a alpha `<=` @HolomorphicSetIdeal.value R X NX hNX a beta ->
  set_germ_subset beta alpha.
Proof.
move=>hAlpha hIdeal.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [J [f [U [ha [hU [hAnalytic hAlphaEquation]]]]]]:=
  @holomorphic_variety_germ_equation_system R X NX hNX a alpha hAlpha.
have [S hS]:=@set_germ_has_representative T a beta.
rewrite -hS -hAlphaEquation.
apply:(@finite_holomorphic_germ_vanishing_containment R X NX hNX a J f U S ha hU)=>j.
have hGenerator:=@finite_holomorphic_germ_zero_system_generators_vanish R X NX hNX a J f U ha hU j.
rewrite hAlphaEquation in hGenerator.
have hBeta:=hIdeal _ hGenerator.
by rewrite hS.
Qed.

(** Source for [holomorphic_variety_germ_ideal_injective]:
    actual analytic variety germs with equal ideals are
    equal, supporting the original recovery and component
    assertions of 3.4.5, pp. 320–321. *)
Lemma holomorphic_variety_germ_ideal_injective (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  @is_holomorphic_variety_germ R X NX hNX a beta ->
  @HolomorphicSetIdeal.value R X NX hNX a alpha=@HolomorphicSetIdeal.value R X NX hNX a beta ->alpha=beta.
Proof.
move=>hAlpha hBeta hEqual;apply:set_germ_subset_antisymmetric.
- apply:(@holomorphic_variety_germ_ideal_separation R X NX hNX a beta alpha hBeta).
  by rewrite hEqual.
- apply:(@holomorphic_variety_germ_ideal_separation R X NX hNX a alpha beta hAlpha).
  by rewrite hEqual.
Qed.
