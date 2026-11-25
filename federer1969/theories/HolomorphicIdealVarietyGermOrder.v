(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    recover variety containment from the original
    finite equations of 3.4.5, p. 320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  SetGermUP SetGermLaws SetGermOrder CommutativeIdealUP HolomorphicGermVanishingSealed
  FiniteHolomorphicGermGenerators FiniteHolomorphicGermVanishingContainment HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed
  HolomorphicIdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section VarietyOrder.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX a).
Local Notation var I hI:=(@HolomorphicIdealVarietyGerm.value R X NX hNX a I hI).

(** Source for [ideal_variety_germ_contains_vanishing_set]:
    the finite generator definition of var(I),
    3.4.5, p. 320, applied to the
    equation-ideal argument of 3.4.8(10), p. 331.
    A set germ annihilating I lies in var(I). *)
Theorem ideal_variety_germ_contains_vanishing_set (I:set G)
    (hI:is_finitely_generated_commutative_ideal I) (sigma:@set_germ_space T a):
  I `<=` ideal sigma ->set_germ_subset sigma (var I hI).
Proof.
move=>hVanish.
have [J [f [U [ha [hU [hHolomorphic hGenerated]]]]]]:=
  @finite_holomorphic_germ_generator_system_exists R X NX hNX a I hI.
have [S hS]:=@set_germ_has_representative T a sigma.
rewrite -hS in hVanish *.
rewrite (@holomorphic_ideal_variety_germ_original_equation R X NX hNX a I (var I hI)
  (@HolomorphicIdealVarietyGerm.laws R X NX hNX a I hI) J f U ha hU hHolomorphic hGenerated).
apply:(@finite_holomorphic_germ_vanishing_containment R X NX hNX a J f U S ha hU)=>j.
apply:hVanish;apply:(generated_commutative_ideal_contains hGenerated);by exists j.
Qed.

(** Source for [ideal_variety_germ_antitone]:
    larger ideals have smaller variety germs,
    by 3.4.5, p. 320; this is
    used in 3.4.8(10), p. 331. *)
Lemma ideal_variety_germ_antitone (I J:set G)
    (hI:is_finitely_generated_commutative_ideal I)
    (hJ:is_finitely_generated_commutative_ideal J):
  I `<=` J ->set_germ_subset (var J hJ) (var I hI).
Proof.
move=>hSubset;apply:ideal_variety_germ_contains_vanishing_set=>alpha hAlpha.
exact:(@ideal_in_vanishing_ideal_of_variety R X NX hNX a J hJ alpha (hSubset alpha hAlpha)).
Qed.
End VarietyOrder.
