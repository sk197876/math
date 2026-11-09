(** Federer (1969), 3.4.5, p. 321: existence
    of a finite irreducible decomposition under the stated
    Noetherian hypothesis. A minimal counterexample would split
    into two strictly smaller germs that already decompose. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder
  SetGermBooleanOrder SetGermFiniteUnion CommutativeIdealUP AnalyticVarietyGermUP AnalyticIrreducibleGermUP
  NoetherianVarietyMinimum IrreducibleGermCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [noetherian_finite_irreducible_germ_cover]:
    every original analytic variety germ is a finite
    union of nonempty irreducible germs, 3.4.5,
    p. 321, under the printed Noetherian hypothesis.
    The empty original germ receives the empty family. *)
Theorem noetherian_finite_irreducible_germ_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):
  is_noetherian_commutative_ring [the comNzRingType of (@analytic_germ_ring R X NX hNX a)] ->
  forall alpha,@is_analytic_variety_germ R X NX hNX a alpha ->
    exists F,@is_finite_irreducible_germ_cover R X NX hNX a alpha F.
Proof.
move=>hNoetherian.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose G:=@set_germ_space T a.
pose V:=@is_analytic_variety_germ R X NX hNX a.
pose IR:=@is_union_irreducible_analytic_germ R X NX hNX a.
pose cover:=@is_finite_irreducible_germ_cover R X NX hNX a.
pose H:set G:=fun alpha=>V alpha /\~exists F,cover alpha F.
have hNoBad:~exists alpha,H alpha.
  move=>hBad.
  have [alpha [[hAlpha hNoCover] hMinimal]]:=@noetherian_analytic_variety_family_minimum R X NX hNX a H
    hNoetherian hBad (fun alpha hAlpha=>hAlpha.1).
  have hNonempty:alpha<>@set_germ T a set0.
    move=>hEmpty;apply:hNoCover;exists [::];constructor.
    - by move=>beta;rewrite in_nil.
    - exact:esym hEmpty.
  have hNotIrreducible:~IR alpha.
    move=>hIR;apply:hNoCover;exists [::alpha];constructor.
    - move=>beta;rewrite in_cons in_nil orbF=>/eqP ->;by split.
    - exact:(set_germ_union_empty alpha).
  have hSplit:exists beta gamma,V beta /\V gamma /\
      alpha=@SetGerms.join T a beta gamma /\alpha<>beta /\alpha<>gamma.
    case:(pselect (exists beta gamma,V beta /\V gamma /\
      alpha=@SetGerms.join T a beta gamma /\alpha<>beta /\alpha<>gamma))=>[h|h];first exact:h.
    exfalso;apply:hNotIrreducible;split;first exact:hAlpha.
    move=>beta gamma hBeta hGamma hUnion.
    case:(pselect (alpha=beta))=>[hEqual|hDifferent];first by left.
    case:(pselect (alpha=gamma))=>[hEqual|hDifferent'];first by right.
    exfalso;apply:h;exists beta,gamma;by split;last split;last split;last split.
  have [beta [gamma [hBeta [hGamma [hUnion [hBetaStrict hGammaStrict]]]]]]:=hSplit.
  have hBetaContained:set_germ_subset beta alpha by rewrite hUnion;exact:set_germ_subset_join_left.
  have hGammaContained:set_germ_subset gamma alpha by rewrite hUnion;exact:set_germ_subset_join_right.
  have hBetaCover:exists F,cover beta F.
    apply:contrapT=>hNot;have hReverse:=hMinimal beta (conj hBeta hNot) hBetaContained.
    apply:hBetaStrict;exact:set_germ_subset_antisymmetric hReverse hBetaContained.
  have hGammaCover:exists F,cover gamma F.
    apply:contrapT=>hNot;have hReverse:=hMinimal gamma (conj hGamma hNot) hGammaContained.
    apply:hGammaStrict;exact:set_germ_subset_antisymmetric hReverse hGammaContained.
  have [F hF]:=hBetaCover;have [K hK]:=hGammaCover.
  apply:hNoCover;exists (F++K);constructor.
  - move=>eta;rewrite mem_cat=>/orP [hEta|hEta].
    + exact:(@irreducible_germ_cover_members R X NX hNX a beta F hF eta hEta).
    + exact:(@irreducible_germ_cover_members R X NX hNX a gamma K hK eta hEta).
  - by rewrite set_germ_finite_union_cat (irreducible_germ_cover_union hF)
      (irreducible_germ_cover_union hK) -hUnion.
move=>alpha hAlpha;apply:contrapT=>hNone;apply:hNoBad;exists alpha;by split.
Qed.
