(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 321: complete
    finite maximal-component decomposition and the original
    ideal-intersection formula under the stated Noetherian
    hypothesis. All component choices remain behind their seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing SetGermUP SetGermOrder SetGermFiniteUnion
  CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingUnion HolomorphicVarietyGermUP HolomorphicIrreducibleGermUP
  HolomorphicIrreducibleGermCoverUP NoetherianHolomorphicIrreducibleCover HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleComponentsSealed
  HolomorphicIrreducibleComponentsFinite HolomorphicIrreducibleComponentsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [noetherian_holomorphic_irreducible_component_decomposition]:
    the original germ is the union of its unique finite
    maximal irreducible component family; no distinct component
    contains another; its ideal is the intersection of all
    original component ideals, 3.4.5, p. 321.
    Nonempty components give the empty germ its empty family. *)
Theorem noetherian_holomorphic_irreducible_component_decomposition (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  is_noetherian_commutative_ring [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)] ->
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  finite_set (@HolomorphicIrreducibleComponents.value R X NX hNX a alpha) /\
  (exists K,@is_finite_irreducible_holomorphic_germ_cover R X NX hNX a alpha K /\
    @HolomorphicIrreducibleComponents.value R X NX hNX a alpha=[set beta|beta \in K]) /\
  (forall beta gamma,@HolomorphicIrreducibleComponents.value R X NX hNX a alpha beta ->
    @HolomorphicIrreducibleComponents.value R X NX hNX a alpha gamma ->set_germ_subset beta gamma ->beta=gamma) /\
  @HolomorphicSetIdeal.value R X NX hNX a alpha=
    \bigcap_(beta in @HolomorphicIrreducibleComponents.value R X NX hNX a alpha)
      @HolomorphicSetIdeal.value R X NX hNX a beta.
Proof.
move=>hNoetherian hAlpha.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose C:=@HolomorphicIrreducibleComponents.value R X NX hNX a alpha.
have hLaws:=@HolomorphicIrreducibleComponents.laws R X NX hNX a alpha.
have [F hF]:=@noetherian_finite_irreducible_holomorphic_germ_cover R X NX hNX a hNoetherian alpha hAlpha.
have [K [hC hUnion]]:=@finite_holomorphic_irreducible_components_from_cover R X NX hNX a alpha F hF.
have hCover:@is_finite_irreducible_holomorphic_germ_cover R X NX hNX a alpha K.
  constructor;last exact:hUnion.
  move=>beta hBeta.
  have hComponent:C beta by rewrite /C hC.
  exact:((holomorphic_irreducible_component_membership hLaws beta).1 hComponent).1.
split.
- rewrite hC;exact:finite_seq.
- split;first by exists K;split.
  split;first exact:(@holomorphic_irreducible_components_antichain R X NX hNX a alpha).
  apply/seteqP;split.
  + move=>f hVan beta hBeta.
    have hK:[set gamma|gamma \in K] beta by rewrite -hC.
    rewrite -hUnion in hVan.
    exact:((@holomorphic_set_ideal_finite_union R X NX hNX a K f).1 hVan beta hK).
  + move=>f hVan;rewrite -hUnion;apply/(@holomorphic_set_ideal_finite_union R X NX hNX a K f)=>beta hBeta.
    apply:hVan;by rewrite hC.
Qed.
