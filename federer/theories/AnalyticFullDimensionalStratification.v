(** Federer (1969), corrected 3.4.8(11), pp. 327, 333:
    complete the n=m induction case. The original
    germ fills the source; an original nonzero equation
    gives the smaller-dimensional exceptional variety. The
    critical maximum argument supplies actual finite components
    of the final regular ball, and the corrected
    assembly retains the original representative and S0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology NormAnalyticUP NormAnalyticOperations AnalyticGermRepresentatives AnalyticGermNeighbourhood
  AnalyticGermUP AnalyticGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder
  SetGermLocality FiniteAnalyticVarietyUP FiniteAnalyticVarietyRestriction AnalyticVarietyGermUP
  GermVanishingSealed AnalyticDepthSealed AnalyticZeroGermSealed AnalyticFullDimensionalCut
  AnalyticFiniteStratificationUP AnalyticStratificationInductionUP AnalyticStratificationLowerLocal
  AnalyticStratificationExceptionalInduction AnalyticStratificationRegularAssembly AnalyticEmptyStratification
  AnalyticVarietyCutLocalData AnalyticGermNonzeroLocusBoundary AnalyticNonzeroNeighbourhoodChoice InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullStratification.
Variable R:realType.
Variable n:nat.
Hypothesis hInduction:forall d,(d<n.+1)%N ->analytic_stratification_at_bound R d.
Local Notation X:=(R_n R n.+1).
Local Notation B:=(@euclidean_inner_product R n.+1).
Local Notation hB:=(@euclidean_inner_productP R n.+1).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n.+1 (@coordinate_basis R n.+1)
  (@coordinate_basisP R n.+1) (dual_basis (@coordinate_basisP R n.+1))).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_full_dimensional_stratification_from_induction]:
    every original assertion of the n=m case
    of 3.4.8(11), p. 333, with the
    complete published boundary correction at p. 327
    line 24. The smaller-depth induction is explicit;
    all analytic equations and finite-component choices are proved. *)
Theorem analytic_full_dimensional_stratification_from_induction (U H U0 S0:set X):
  U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
  U0 0 ->@is_finite_analytic_variety R X NX hNX U0 S0 ->
  germ H<>germ set0 ->depth (ideal (germ H)) = n.+1 ->
  exists mu,exists V S G:'I_mu->set X,
    @is_analytic_finite_stratification R n.+1 (germ H) (germ S0) n.+1 U0 S0 mu V S G /\
    forall i,S i `<=` H.
Proof.
move=>hU0 hH hU00 hS0 hNonempty hDepth.
have hDual i j:dual_basis (@coordinate_basisP R n.+1) i (@coordinate_basis R n.+1 j) =
    if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hAlpha:@is_analytic_variety_germ R X NX hNX 0 (germ H).
  exists U,H;split;first exact:hU0.
  by split.
have hBeta:@is_analytic_variety_germ R X NX hNX 0 (germ S0).
  exists U0,S0;split;first exact:hU00.
  by split.
have hWhole:=@analytic_full_dimensional_variety_whole R X B hB n (@coordinate_basis R n.+1)
  (@coordinate_basisP R n.+1) (@euclidean_coordinate_orthonormal_family R n.+1)
  (dual_basis (@coordinate_basisP R n.+1)) hDual (germ H) hAlpha hNonempty hDepth.
case:(pselect (germ S0 = germ setT))=>hBetaWhole.
- have hEmpty:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hBetaWhole (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setCT
      (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setI0.
    reflexivity.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:analytic_empty_stratification hEmpty.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have [f [hFNonzero [hFVanish [hBetaGamma hDrop]]]]:=
    @analytic_full_dimensional_exceptional_equation R X B hB n (@coordinate_basis R n.+1)
      (@coordinate_basisP R n.+1) (@euclidean_coordinate_orthonormal_family R n.+1)
      (dual_basis (@coordinate_basisP R n.+1)) hDual (germ S0) hBeta hBetaWhole.
  pose phi:=analytic_representative_value f.
  pose gamma:=@AnalyticZeroGerm.value R X NX hNX 0 (analytic_germ f).
  pose D:set X:=[set x|phi x<>0].
  have [F [hF0 [_ [hFOpen hFAnalytic]]]]:=analytic_germ_open_representative (analytic_representative_analytic f).
  pose U1:set X:=U `&` F.
  pose H1:set X:=U1 `&` H.
  have hU1:@open T U1:=openI hH.1 hFOpen.
  have hU10:U1 0 by split.
  have hH1:=@finite_analytic_variety_open_restriction R X NX hNX U U1 H hH hU1 (fun x hx=>hx.1).
  have hH1Germ:germ H1 = germ H:=@set_germ_neighbourhood_intersection T 0 U1 H hU1 hU10.
  have hInterior x (hx:U1 x):norm_domain_interior NX U1 x.
    have hOpen:=hU1;rewrite openE in hOpen.
    exact:(@norm_domain_interior_neighbourhood R X NX hNX U1 x).2 (hOpen x hx).
  have hPhi:=@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) F U1 phi (fun x hx=>hx.2) hInterior hFAnalytic.
  have hGamma:gamma = germ [set x|phi x=0].
    exact:esym (@AnalyticZeroGerm.laws R X NX hNX 0 _ f (erefl _)).
  have hCut:gamma = @SetGerms.meet T 0 (germ H1) (germ [set x|phi x=0]).
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole;exact:hGamma.
  have hRegular:germ D = @SetGerms.meet T 0 (germ H1) (@SetGerms.neg T 0 gamma).
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole
      hGamma (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)).
    reflexivity.
  have hContained:set_germ_subset (@SetGerms.meet T 0 (germ H1) (germ S0)) gamma.
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole;exact:hBetaGamma.
  have [A [E [hA [hA0 [hAU1 [hE [hEGerm [hEH1 [hDInside [hDE hBoundary]]]]]]]]]]:=
    @analytic_variety_cut_local_data R X NX hNX U1 H1 D S0 phi gamma hU10 hH1 hPhi hCut hRegular hContained.
  have hEDrop:germ E = germ set0 \/(depth (ideal (germ E))<n.+1)%N by rewrite hEGerm.
  have [mu [V [S [G [hOld hOldInside]]]]]:=@analytic_exceptional_stratification_from_induction
    R n.+1 hInduction n.+1 A E U0 S0 hA0 hE hU00 hS0 hEDrop.
  rewrite hEGerm in hOld.
  have hAInterior x (hx:A x):norm_domain_interior NX A x.
    have hOpen:=hA;rewrite openE in hOpen.
    exact:(@norm_domain_interior_neighbourhood R X NX hNX A x).2 (hOpen x hx).
  have hPhiA:=@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) U1 A phi hAU1 hAInterior hPhi.
  have hFunctional:=(@analytic_nonzero_locus_functional_boundary R n.+1 A phi hA hPhiA).1.
  have hGammaAlpha:set_germ_subset gamma (germ H).
    rewrite hWhole /set_germ_subset set_germ_intersection_whole;reflexivity.
  have hABGamma:set_germ_subset (@SetGerms.meet T 0 (germ H) (germ S0)) gamma.
    by rewrite -hH1Germ.
  have hRegularOriginal:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 gamma) = germ D.
    by rewrite -hH1Germ -hRegular.
  have hLower (W L:set X) (hW0:W 0)
      (hL:@is_finite_analytic_variety R X NX hNX W L)
      (hNonemptyL:germ L<>germ set0)
      (hSmall:(depth (ideal (germ L))<n.+1)%N):
      exists O:set X,@open T O /\O 0 /\
        finite_set (@connected_component T L @` (L `&` O)).
    exact:(@analytic_stratification_lower_local_components R n.+1 hInduction n.+1 W L hW0 hL hSmall).
  have hChoice:=@analytic_nonzero_neighbourhood_choice R n U1 phi hU10 hPhi hLower.
  have [Vnew [Snew [Gnew [hLaws hInside]]]]:=@analytic_stratification_regular_assembly R n.+1
    (germ H) (germ S0) gamma n.+1 n.+1 A H E D U0 S0 mu V S G
    hA hA0 hU00 hS0.1 (erefl _) hEGerm hGammaAlpha hABGamma hRegularOriginal hE
    hFunctional (leqnn n.+1) hEDrop (fun x hx=>(hEH1 x hx).2)
    (fun x hx hAx=>conj (hDInside x hx hAx).1.2 (hDInside x hx hAx).2)
    hDE hBoundary hOld hOldInside (fun W hW hW0 _=>@hChoice W hW hW0).
  exists mu.+1,(ordinal_snoc V Vnew),(ordinal_snoc S Snew),(ordinal_snoc G Gnew).
  by split.
Qed.
End FullStratification.
