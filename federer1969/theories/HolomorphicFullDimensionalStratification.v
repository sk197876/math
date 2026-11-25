(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    complete the n=m induction case. The original
    germ fills the source; an original nonzero equation
    gives the smaller-dimensional exceptional variety. The
    proved real component theorem supplies actual finite components
    of the final regular ball, and the corrected
    assembly retains the original representative and S0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import StandardHermitianBasisValues FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology HolomorphicUP HolomorphicRestriction HolomorphicGermRepresentatives HolomorphicGermNeighbourhood
  HolomorphicGermUP HolomorphicGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder
  SetGermLocality FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRestriction HolomorphicVarietyGermUP
  HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicZeroGermSealed HolomorphicFullDimensionalCut
  HolomorphicFiniteStratificationUP HolomorphicStratificationInductionUP HolomorphicDifferenceGermFiniteNeighbourhood
  HolomorphicStratificationExceptionalInduction HolomorphicStratificationRegularAssembly HolomorphicEmptyStratification
  HolomorphicVarietyCutLocalData HolomorphicGermNonzeroLocusBoundary HolomorphicDifferenceGermFiniteNeighbourhood InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullStratification.
Variable R:realType.
Variable n:nat.
Hypothesis hInduction:forall d,(d<n.+1)%N ->holomorphic_stratification_at_bound R d.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n.+1).
Local Notation Herm:=(@standard_hermitian_product R n.+1).
Local Notation hHerm:=(@standard_hermitian_productP R n.+1).
Local Notation NX:=(@holomorphic_coordinate_norm R n.+1).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n.+1)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n.+1 (@coordinate_basis (ComplexScalars.C R) n.+1)
  (@coordinate_basisP (ComplexScalars.C R) n.+1) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1))).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).

(** Source for [holomorphic_full_dimensional_stratification_from_induction]:
    every original assertion of the n=m case
    of 3.4.12, p. 339, extending 3.4.8(11), p. 333, with the
    complete published boundary correction at p. 327
    line 24. The smaller-depth induction is explicit;
    all holomorphic equations and finite-component choices are proved. *)
Theorem holomorphic_full_dimensional_stratification_from_induction (U H U0 S0:set X):
  U 0 ->@is_finite_holomorphic_variety R X NX hNX U H ->
  U0 0 ->@is_finite_holomorphic_variety R X NX hNX U0 S0 ->
  germ H<>germ set0 ->depth (ideal (germ H)) = n.+1 ->
  exists mu,exists V S G:'I_mu->set X,
    @is_holomorphic_finite_stratification R n.+1 (germ H) (germ S0) n.+1 U0 S0 mu V S G /\
    forall i,S i `<=` H.
Proof.
move=>hU0 hH hU00 hS0 hNonempty hDepth.
have hDual i j:dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1) i (@coordinate_basis (ComplexScalars.C R) n.+1 j) =
    if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hAlpha:@is_holomorphic_variety_germ R X NX hNX 0 (germ H).
  exists U,H;split;first exact:hU0.
  by split.
have hBeta:@is_holomorphic_variety_germ R X NX hNX 0 (germ S0).
  exists U0,S0;split;first exact:hU00.
  by split.
have hWhole:=@holomorphic_full_dimensional_variety_whole R X Herm hHerm n (@coordinate_basis (ComplexScalars.C R) n.+1)
  (@coordinate_basisP (ComplexScalars.C R) n.+1) (@standard_hermitian_basis_orthonormal R n.+1)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1)) hDual (germ H) hAlpha hNonempty hDepth.
case:(pselect (germ S0 = germ setT))=>hBetaWhole.
- have hEmpty:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hBetaWhole (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setCT
      (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setI0.
    reflexivity.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:holomorphic_empty_stratification hEmpty.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have [f [hFNonzero [hFVanish [hBetaGamma hDrop]]]]:=
    @holomorphic_full_dimensional_exceptional_equation R X Herm hHerm n (@coordinate_basis (ComplexScalars.C R) n.+1)
      (@coordinate_basisP (ComplexScalars.C R) n.+1) (@standard_hermitian_basis_orthonormal R n.+1)
      (dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1)) hDual (germ S0) hBeta hBetaWhole.
  pose phi:=holomorphic_representative_value f.
  pose gamma:=@HolomorphicZeroGerm.value R X NX hNX 0 (holomorphic_germ f).
  pose D:set X:=[set x|phi x<>0].
  have [F [hF0 [_ [hFOpen hFHolomorphic]]]]:=holomorphic_germ_open_representative f.
  pose U1:set X:=U `&` F.
  pose H1:set X:=U1 `&` H.
  have hU1:@open T U1:=openI hH.1 hFOpen.
  have hU10:U1 0 by split.
  have hH1:=@finite_holomorphic_variety_open_restriction R X NX hNX U U1 H hH hU1 (fun x hx=>hx.1).
  have hH1Germ:germ H1 = germ H:=@set_germ_neighbourhood_intersection T 0 U1 H hU1 hU10.
  have hInterior x (hx:U1 x):@norm_domain_interior R XR NX U1 x.
    have hOpen:=hU1;rewrite openE in hOpen.
    exact:(@norm_domain_interior_neighbourhood R XR NX hNX U1 x).2 (hOpen x hx).
  have hPhi:=@holomorphic_open_restriction R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) F U1 phi (fun x hx=>hx.2) hInterior hFHolomorphic.
  have hGamma:gamma = germ [set x|phi x=0].
    exact:esym (@HolomorphicZeroGerm.laws R X NX hNX 0 _ f (erefl _)).
  have hCut:gamma = @SetGerms.meet T 0 (germ H1) (germ [set x|phi x=0]).
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole;exact:hGamma.
  have hRegular:germ D = @SetGerms.meet T 0 (germ H1) (@SetGerms.neg T 0 gamma).
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole
      hGamma (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)).
    reflexivity.
  have hContained:set_germ_subset (@SetGerms.meet T 0 (germ H1) (germ S0)) gamma.
    rewrite hH1Germ hWhole set_germ_intersection_commutative set_germ_intersection_whole;exact:hBetaGamma.
  have [A [E [hA [hA0 [hAU1 [hE [hEGerm [hEH1 [hDInside [hDE hBoundary]]]]]]]]]]:=
    @holomorphic_variety_cut_local_data R X NX hNX U1 H1 D S0 phi gamma hU10 hH1 hPhi hCut hRegular hContained.
  have hEDrop:germ E = germ set0 \/(depth (ideal (germ E))<n.+1)%N by rewrite hEGerm.
  have [mu [V [S [G [hOld hOldInside]]]]]:=@holomorphic_exceptional_stratification_from_induction
    R n.+1 hInduction n.+1 A E U0 S0 hA0 hE hU00 hS0 hEDrop.
  rewrite hEGerm in hOld.
  have hAInterior x (hx:A x):@norm_domain_interior R XR NX A x.
    have hOpen:=hA;rewrite openE in hOpen.
    exact:(@norm_domain_interior_neighbourhood R XR NX hNX A x).2 (hOpen x hx).
  have hPhiA:=@holomorphic_open_restriction R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) U1 A phi hAU1 hAInterior hPhi.
  have hFunctional:=(@holomorphic_nonzero_locus_functional_boundary R n.+1 A phi hA hPhiA).1.
  have hGammaAlpha:set_germ_subset gamma (germ H).
    rewrite hWhole /set_germ_subset set_germ_intersection_whole;reflexivity.
  have hABGamma:set_germ_subset (@SetGerms.meet T 0 (germ H) (germ S0)) gamma.
    by rewrite -hH1Germ.
  have hRegularOriginal:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 gamma) = germ D.
    by rewrite -hH1Germ -hRegular.

  have hEVariety:@is_holomorphic_variety_germ R X NX hNX 0 (germ E).
    exists A,E;split;first exact:hA0;by split.
  have hDifference:germ D = germ (H `\` E).
    have hFormula:germ (H `\` E) = @SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ E)).
      by rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
        (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
    rewrite hFormula hEGerm;exact:esym hRegularOriginal.
  have hChoice:=@holomorphic_difference_germ_finite_neighbourhood R n.+1 H E D hAlpha hEVariety hDifference.
  have [Vnew [Snew [Gnew [hLaws hInside]]]]:=@holomorphic_stratification_regular_assembly R n.+1
    (germ H) (germ S0) gamma n.+1 n.+1 A H E D U0 S0 mu V S G
    hA hA0 hU00 hS0.1 (erefl _) hEGerm hGammaAlpha hABGamma hRegularOriginal hE
    hFunctional (leqnn n.+1) hEDrop (fun x hx=>(hEH1 x hx).2)
    (fun x hx hAx=>conj (hDInside x hx hAx).1.2 (hDInside x hx hAx).2)
    hDE hBoundary hOld hOldInside (fun W hW hW0 _=>@hChoice W hW hW0).
  exists mu.+1,(ordinal_snoc V Vnew),(ordinal_snoc S Snew),(ordinal_snoc G Gnew).
  by split.
Qed.
End FullStratification.
