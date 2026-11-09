(** Federer (1969), 3.4.5, p. 321: complete
    finite maximal-component decomposition and the original
    ideal-intersection formula under the stated Noetherian
    hypothesis. All component choices remain behind their seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP SetGermOrder SetGermFiniteUnion
  CommutativeIdealUP GermVanishingSealed GermVanishingUnion AnalyticVarietyGermUP AnalyticIrreducibleGermUP
  IrreducibleGermCoverUP NoetherianIrreducibleCover IrreducibleComponentsUP IrreducibleComponentsSealed
  IrreducibleComponentsFinite IrreducibleComponentsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [noetherian_irreducible_component_decomposition]:
    the original germ is the union of its unique finite
    maximal irreducible component family; no distinct component
    contains another; its ideal is the intersection of all
    original component ideals, 3.4.5, p. 321.
    Nonempty components give the empty germ its empty family. *)
Theorem noetherian_irreducible_component_decomposition (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  is_noetherian_commutative_ring [the comNzRingType of (@analytic_germ_ring R X NX hNX a)] ->
  @is_analytic_variety_germ R X NX hNX a alpha ->
  finite_set (@IrreducibleComponents.value R X NX hNX a alpha) /\
  (exists K,@is_finite_irreducible_germ_cover R X NX hNX a alpha K /\
    @IrreducibleComponents.value R X NX hNX a alpha=[set beta|beta \in K]) /\
  (forall beta gamma,@IrreducibleComponents.value R X NX hNX a alpha beta ->
    @IrreducibleComponents.value R X NX hNX a alpha gamma ->set_germ_subset beta gamma ->beta=gamma) /\
  @AnalyticSetIdeal.value R X NX hNX a alpha=
    \bigcap_(beta in @IrreducibleComponents.value R X NX hNX a alpha)
      @AnalyticSetIdeal.value R X NX hNX a beta.
Proof.
move=>hNoetherian hAlpha.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose C:=@IrreducibleComponents.value R X NX hNX a alpha.
have hLaws:=@IrreducibleComponents.laws R X NX hNX a alpha.
have [F hF]:=@noetherian_finite_irreducible_germ_cover R X NX hNX a hNoetherian alpha hAlpha.
have [K [hC hUnion]]:=@finite_irreducible_components_from_cover R X NX hNX a alpha F hF.
have hCover:@is_finite_irreducible_germ_cover R X NX hNX a alpha K.
  constructor;last exact:hUnion.
  move=>beta hBeta.
  have hComponent:C beta by rewrite /C hC.
  exact:((irreducible_component_membership hLaws beta).1 hComponent).1.
split.
- rewrite hC;exact:finite_seq.
- split;first by exists K;split.
  split;first exact:(@irreducible_components_antichain R X NX hNX a alpha).
  apply/seteqP;split.
  + move=>f hVan beta hBeta.
    have hK:[set gamma|gamma \in K] beta by rewrite -hC.
    rewrite -hUnion in hVan.
    exact:((@analytic_set_ideal_finite_union R X NX hNX a K f).1 hVan beta hK).
  + move=>f hVan;rewrite -hUnion;apply/(@analytic_set_ideal_finite_union R X NX hNX a K f)=>beta hBeta.
    apply:hVan;by rewrite hC.
Qed.
