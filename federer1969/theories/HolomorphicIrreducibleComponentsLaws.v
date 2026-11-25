(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 321: original
    irreducible components form an antichain, and their
    intrinsic maximality determines every irredundant decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric SetGermUP SetGermOrder SetGermFiniteUnion
  HolomorphicVarietyGermUP HolomorphicIrreducibleGermUP HolomorphicIrreducibleUnionBound
  HolomorphicIrreducibleGermCoverUP HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleComponentsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Components.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T a).
Local Notation NI:=(@is_nonempty_irreducible_holomorphic_germ R X NX hNX a).
Local Notation C alpha:=(@HolomorphicIrreducibleComponents.value R X NX hNX a alpha).

(** Source for [holomorphic_irreducible_components_antichain]: one
    original component can contain another only when they
    are equal, 3.4.5, p. 321. *)
Lemma holomorphic_irreducible_components_antichain (alpha beta gamma:G):
  C alpha beta ->C alpha gamma ->set_germ_subset beta gamma ->beta=gamma.
Proof.
move=>hBeta hGamma hContained.
have [hBetaNI [hBetaInside hMaximum]]:=(holomorphic_irreducible_component_membership (HolomorphicIrreducibleComponents.laws alpha) beta).1 hBeta.
have [hGammaNI [hGammaInside _]]:=(holomorphic_irreducible_component_membership (HolomorphicIrreducibleComponents.laws alpha) gamma).1 hGamma.
apply:set_germ_subset_antisymmetric;first exact:hContained.
exact:hMaximum gamma hGammaNI hGammaInside hContained.
Qed.

(** Source for [irreducible_cover_member_is_component]:
    every member of an irredundant original finite
    irreducible cover is a maximal irreducible component,
    3.4.5, p. 321. *)
Lemma irreducible_cover_member_is_component (alpha:G) (F:seq G):
  @is_finite_irreducible_holomorphic_germ_cover R X NX hNX a alpha F ->
  (forall beta gamma,beta \in F ->gamma \in F ->set_germ_subset beta gamma ->beta=gamma) ->
  forall beta,beta \in F ->C alpha beta.
Proof.
move=>hCover hAntichain beta hBeta.
have hNI eta (hEta:eta \in F):NI eta.
  exact:(@irreducible_holomorphic_germ_cover_members R X NX hNX a alpha F hCover eta hEta).
have hV eta (hEta:eta \in F):@is_holomorphic_variety_germ R X NX hNX a eta:=(hNI eta hEta).1.1.
have hUnion:=@irreducible_holomorphic_germ_cover_union R X NX hNX a alpha F hCover.
apply/(holomorphic_irreducible_component_membership (HolomorphicIrreducibleComponents.laws alpha) beta).
split;first exact:hNI beta hBeta.
split.
- rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
- move=>gamma hGamma hInside hContained.
  have hInUnion:set_germ_subset gamma (@set_germ_finite_union T a F) by rewrite hUnion.
  have [eta [hEta hGammaEta]]:=@irreducible_variety_finite_union_bound R X NX hNX a gamma F hGamma hV hInUnion.
  have hBetaEta:=set_germ_subset_transitive hContained hGammaEta.
  have hEqual:=hAntichain beta eta hBeta hEta hBetaEta.
  by rewrite hEqual.
Qed.

(** Source for [irreducible_cover_unique_members]: every
    irredundant original finite irreducible family has exactly
    the intrinsic component members, establishing uniqueness
    of the family in 3.4.5, p. 321. *)
Theorem irreducible_cover_unique_members (alpha:G) (F:seq G):
  @is_finite_irreducible_holomorphic_germ_cover R X NX hNX a alpha F ->
  (forall beta gamma,beta \in F ->gamma \in F ->set_germ_subset beta gamma ->beta=gamma) ->
  C alpha=[set beta|beta \in F].
Proof.
move=>hCover hAntichain;apply/seteqP;split.
- move=>beta hBeta.
  have [hNI [hInside hMaximum]]:=(holomorphic_irreducible_component_membership (HolomorphicIrreducibleComponents.laws alpha) beta).1 hBeta.
  have hV eta (hEta:eta \in F):@is_holomorphic_variety_germ R X NX hNX a eta.
    exact:(@irreducible_holomorphic_germ_cover_members R X NX hNX a alpha F hCover eta hEta).1.1.
  have hInUnion:set_germ_subset beta (@set_germ_finite_union T a F).
    by rewrite (irreducible_holomorphic_germ_cover_union hCover).
  have [gamma [hGamma hBetaGamma]]:=@irreducible_variety_finite_union_bound R X NX hNX a beta F hNI hV hInUnion.
  have hGammaNI:=@irreducible_holomorphic_germ_cover_members R X NX hNX a alpha F hCover gamma hGamma.
  have hGammaInside:set_germ_subset gamma alpha.
    rewrite -(irreducible_holomorphic_germ_cover_union hCover);exact:set_germ_finite_union_member hGamma.
  have hReverse:=hMaximum gamma hGammaNI hGammaInside hBetaGamma.
  have hEqual:=set_germ_subset_antisymmetric hBetaGamma hReverse.
  by rewrite hEqual.
- move=>beta hBeta;exact:(@irreducible_cover_member_is_component alpha F hCover hAntichain beta hBeta).
Qed.
End Components.
