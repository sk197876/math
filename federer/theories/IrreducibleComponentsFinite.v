(** Federer (1969), 3.4.5, p. 321: any
    finite irreducible cover yields exactly the finite family
    of maximal irreducible components, with the original union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP SetGermOrder SetGermFiniteUnion
  FinitePreorderMaximum AnalyticVarietyGermUP AnalyticIrreducibleGermUP AnalyticIrreducibleUnionBound
  IrreducibleGermCoverUP IrreducibleComponentsUP IrreducibleComponentsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_irreducible_components_from_cover]:
    maximal irreducible members form a finite family whose
    union is the original germ, 3.4.5, p. 321.
    Finiteness and the exact union are proved from an
    actual finite irreducible cover and the public maximality laws. *)
Theorem finite_irreducible_components_from_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) alpha F:
  @is_finite_irreducible_germ_cover R X NX hNX a alpha F ->
  exists K:seq (@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a),
    @IrreducibleComponents.value R X NX hNX a alpha=[set beta|beta \in K] /\
    @set_germ_finite_union (Topological.clone (real_norm_metric_space hNX) _) a K=alpha.
Proof.
move=>hCover.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose G:=@set_germ_space T a.
pose NI:=@is_nonempty_irreducible_analytic_germ R X NX hNX a.
pose V:=@is_analytic_variety_germ R X NX hNX a.
pose C:=@IrreducibleComponents.value R X NX hNX a alpha.
have hC:=@IrreducibleComponents.laws R X NX hNX a alpha.
have hF beta (hBeta:beta \in F):NI beta.
  exact:(@irreducible_germ_cover_members R X NX hNX a alpha F hCover beta hBeta).
have hVF beta (hBeta:beta \in F):V beta:= (hF beta hBeta).1.1.
have hUnion:=@irreducible_germ_cover_union R X NX hNX a alpha F hCover.
have hInside beta (hBeta:beta \in F):set_germ_subset beta alpha.
  rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
have hComponentInF beta (hBeta:C beta):beta \in F.
  have [hNI [hContained hMax]]:=(irreducible_component_membership hC beta).1 hBeta.
  have hInUnion:set_germ_subset beta (@set_germ_finite_union T a F) by rewrite hUnion.
  have [gamma [hGamma hBetaGamma]]:=@irreducible_variety_finite_union_bound R X NX hNX a beta F hNI hVF hInUnion.
  have hGammaBeta:=hMax gamma (hF gamma hGamma) (hInside gamma hGamma) hBetaGamma.
  have hEqual:=set_germ_subset_antisymmetric hBetaGamma hGammaBeta.
  by rewrite hEqual.
have hAbove beta (hBeta:beta \in F):exists gamma,gamma \in F /\C gamma /\set_germ_subset beta gamma.
  have [gamma [hGamma [hBetaGamma hMaximum]]]:=@finite_preorder_maximum_above_member G
    (@set_germ_subset T a) (@set_germ_subset_reflexive T a)
    (@set_germ_subset_transitive T a) F beta hBeta.
  exists gamma;split;first exact:hGamma.
  split;last exact:hBetaGamma.
  apply/(irreducible_component_membership hC gamma);split;first exact:hF gamma hGamma.
  split;first exact:hInside gamma hGamma.
  move=>delta hDelta hDeltaInside hGammaDelta.
  have hDeltaInUnion:set_germ_subset delta (@set_germ_finite_union T a F) by rewrite hUnion.
  have [eta [hEta hDeltaEta]]:=@irreducible_variety_finite_union_bound R X NX hNX a delta F
    hDelta hVF hDeltaInUnion.
  have hGammaEta:=set_germ_subset_transitive hGammaDelta hDeltaEta.
  have hEtaGamma:=hMaximum eta hEta hGammaEta.
  exact:set_germ_subset_transitive hDeltaEta hEtaGamma.
pose K:seq G:=[seq beta <- F | `[< C beta >]].
have hMember beta:beta \in K <->C beta.
  rewrite /K mem_filter;split.
  - by move/andP=>[/asboolP hBeta _].
  - move=>hBeta;apply/andP;split;[apply/asboolP;exact:hBeta|exact:hComponentInF beta hBeta].
exists K;split.
- apply/seteqP;split=>beta hBeta;[exact:(hMember beta).2 hBeta|exact:(hMember beta).1 hBeta].
- apply:set_germ_subset_antisymmetric.
  + apply:set_germ_finite_union_bound=>beta hBeta.
    exact:((irreducible_component_membership hC beta).1 ((hMember beta).1 hBeta)).2.1.
  + rewrite -hUnion;apply:set_germ_finite_union_bound=>beta hBeta.
    have [gamma [hGamma [hComponent hBetaGamma]]]:=hAbove beta hBeta.
    have hGammaK:gamma \in K:=(hMember gamma).2 hComponent.
    exact:set_germ_subset_transitive hBetaGamma (set_germ_finite_union_member hGammaK).
Qed.
