(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: taking
    the ideal reverses inclusion of original set germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  SetGermUP SetGermLaws SetGermOrder HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_ideal_antitone]: a germ
    vanishing on a larger set germ vanishes on each
    smaller one, supporting 3.4.5, p. 320. *)
Lemma holomorphic_set_ideal_antitone (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (sigma tau:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  set_germ_subset sigma tau ->
  @HolomorphicSetIdeal.value R X NX hNX a tau `<=` @HolomorphicSetIdeal.value R X NX hNX a sigma.
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [S <-]:=@set_germ_has_representative T a sigma.
have [V <-]:=@set_germ_has_representative T a tau.
move/set_germ_subset_original=>[U [hU [ha hSub]]] alpha hAlpha.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
rewrite -hf in hAlpha *.
have [W [hW [hb hZero]]]:=(holomorphic_set_ideal_representative_equation f V).1 hAlpha.
apply/(holomorphic_set_ideal_representative_equation f S).
exists (U `&` W);split;first exact:openI hU hW.
split;first by split.
move=>x hx [hu hw];exact:hZero x (hSub x hx hu) hw.
Qed.
