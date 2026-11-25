(** Federer (1969), corrected 3.4.8(11), pp. 327, 333:
    reduce the original finite irreducible union to
    successive differences. Each next starting set is
    the actual earlier union on an analytic neighbourhood.
    Concatenation preserves every earlier boundary and finite
    component family without restricting the previous strata. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermFiniteUnion
  SetGermLocality SetGermStartingUnion AnalyticVarietyGermUP AnalyticVarietyGermBooleanClosure
  AnalyticIrreducibleUnionBound FiniteAnalyticVarietyUP AnalyticFiniteStratificationUP AnalyticStratificationGermUP
  AnalyticEmptyStratification AnalyticSubgermRepresentative AnalyticGermLocalRepresentative
  OrdinalFamilyConcatenation AnalyticStratificationConcatenation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteFamily.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation union:=(@set_germ_finite_union T 0).
Local Notation V alpha:=(@is_analytic_variety_germ R X NX hNX 0 alpha).
Local Notation STRAT alpha:=(@analytic_stratification_for_germ R n m alpha).

(** Source for [analytic_finite_family_stratification]:
    the complete ordered finite-union reduction of
    3.4.8(11), p. 333. The actual original
    representative is retained. The uniform component
    input is proved separately by the dimension induction;
    no finiteness of the original variety's components is assumed. *)
Theorem analytic_finite_family_stratification (F:seq (@set_germ_space T 0)):
  (forall alpha,alpha \in F ->V alpha) ->
  (forall alpha,alpha \in F ->STRAT alpha) ->STRAT (union F).
Proof.
elim:F=>[|alpha F IH] hVariety hStrata.
- move=>U H U0 S0 hU0 hH hGerm hU00 hS0.
  have hDifference:@SetGerms.meet T 0 (union [::]) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite set_germ_intersection_commutative.
    exact:SetGermBoundary.set_germ_intersection_empty.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:analytic_empty_stratification hDifference.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have hVarietyTail beta (hBeta:beta \in F):V beta.
    apply:hVariety;by rewrite in_cons hBeta orbT.
  have hStrataTail beta (hBeta:beta \in F):STRAT beta.
    apply:hStrata;by rewrite in_cons hBeta orbT.
  have hTail:=IH hVarietyTail hStrataTail.
  have hAlpha:V alpha:=hVariety alpha (mem_head alpha F).
  have hTailVariety:V (union F):=finite_union_analytic_variety_germ hVarietyTail.
  move=>U H U0 S0 hU0 hH hGerm hU00 hS0.
  have hAlphaInside:set_germ_subset alpha (germ H).
    rewrite hGerm;exact:set_germ_subset_join_left.
  have hTailInside:set_germ_subset (union F) (germ H).
    rewrite hGerm;exact:set_germ_subset_join_right.
  have [U1 [H1 [hU10 [hH1 [hH1Germ [hH1Inside hU1U]]]]]]:=
    @analytic_subgerm_representative_inside R X NX hNX U H alpha hU0 hH.1 hAlpha hAlphaInside.
  have [mu [V1 [S1 [G1 [hFirst hFirstInside]]]]]:=@hStrata alpha (mem_head alpha F)
    U1 H1 U0 S0 hU10 hH1 hH1Germ hU00 hS0.
  pose B0:set X:=S0 `|` \bigcup_i S1 i.
  have hStart:germ B0 = @SetGerms.join T 0 (germ S0) alpha.
    exact:(@set_germ_difference_starting_union T 0 alpha S0 (\bigcup_i S1 i)
      (analytic_stratification_germ hFirst)).
  have hBeta:V (germ S0).
    exists U0,S0;split;first exact:hU00.
    by split.
  have hStartVariety:V (germ B0).
    rewrite hStart;exact:analytic_variety_germ_union hBeta hAlpha.
  have [W [hW0 [hWU0 hStartingVariety]]]:=@analytic_germ_local_representative R X NX hNX U0 B0
    hU00 hS0.1 hStartVariety.
  have hStartingGerm:germ (W `&` B0) = @SetGerms.join T 0 (germ S0) alpha.
    rewrite (@set_germ_neighbourhood_intersection T 0 W B0 hStartingVariety.1 hW0);exact:hStart.
  have [U2 [H2 [hU20 [hH2 [hH2Germ [hH2Inside hU2U]]]]]]:=
    @analytic_subgerm_representative_inside R X NX hNX U H (union F) hU0 hH.1 hTailVariety hTailInside.
  have [nu [V2 [S2 [G2 [hSecond hSecondInside]]]]]:=@hTail U2 H2 W (W `&` B0)
    hU20 hH2 hH2Germ hW0 hStartingVariety.
  rewrite hStartingGerm in hSecond.
  have hCombined:=@analytic_stratification_concatenation R n alpha (union F) (germ S0) m
    U0 S0 W mu nu V1 S1 G1 V2 S2 G2 hFirst hWU0 hSecond.
  exists (mu+nu)%N,(ordinal_family_cat V1 V2),(ordinal_family_cat S1 S2),(ordinal_family_cat G1 G2).
  split;first exact:hCombined.
  move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + move=>x hx;exact:hH1Inside x (hFirstInside j x hx).
  + move=>x hx;exact:hH2Inside x (hSecondInside j x hx).
Qed.
End FiniteFamily.
