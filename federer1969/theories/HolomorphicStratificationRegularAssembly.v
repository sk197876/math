(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333–335:
    choose the final regular neighbourhood after the
    smaller-dimensional strata. Exact germ coverage supplies
    the published earlier-boundary condition on an actual
    neighbourhood; component finiteness is obtained before
    choosing this final stratum, not by arbitrary restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct FiniteDualDimension InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  SetGermLaws SetGermLocality SetGermOrder FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRestriction
  FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicOpenRestriction HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicFiniteStratificationUP HolomorphicStratificationAppend SetGermCutDifference SetGermDifferenceCover
  InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularAssembly.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_stratification_regular_assembly]:
    the full corrected boundary assembly for the
    last regular piece of 3.4.12, p. 339, extending 3.4.8(11), pp. 333–335.
    The actual finite-component neighbourhood is selected
    inside the required cover. The proof does
    not restrict a previously finite component family
    to an arbitrary open set. *)
Theorem holomorphic_stratification_regular_assembly
    (alpha beta gamma:@set_germ_space T 0) m d (A H E D U0 S0:set X)
    mu (V S G:'I_mu->set X):
  @open T A ->A 0 ->U0 0 ->@open T U0 ->
  germ S0 = beta ->germ E = gamma ->
  set_germ_subset gamma alpha ->
  set_germ_subset (@SetGerms.meet T 0 alpha beta) gamma ->
  @SetGerms.meet T 0 alpha (@SetGerms.neg T 0 gamma) = germ D ->
  @is_finite_holomorphic_variety R X NX hNX A E ->
  @is_functional_holomorphic_submanifold R n d A (A `&` D) ->(d<=m)%N ->
  (germ E = germ set0 \/(depth (@HolomorphicSetIdeal.value R X NX hNX 0 (germ E))<m)%N) ->
  E `<=` H ->
  (forall x,D x ->A x ->H x /\~S0 x) ->
  (forall x,D x ->~E x) ->
  A `&` @closure T D `<=` D `|` E ->
  @is_holomorphic_finite_stratification R n gamma beta m U0 S0 mu V S G ->
  (forall i,S i `<=` E) ->
  (forall W:set X,@open T W ->W 0 ->W `<=` A ->
    exists O:set X,@open T O /\O 0 /\O `<=` W /\
      finite_set (@connected_component T (O `&` D) @` (O `&` D))) ->
  exists Vnew Snew Gnew:set X,
    @is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu.+1
      (ordinal_snoc V Vnew) (ordinal_snoc S Snew) (ordinal_snoc G Gnew) /\
    forall i,ordinal_snoc S Snew i `<=` H.
Proof.
move=>hA hA0 hU0 hU0Open hBeta hGamma hGA hABG hRegular hE hD hDM hDepth hEH
  hDInside hDE hBoundary hOld hOldInside hChoose.
have hCovered:@SetGerms.meet T 0 (germ E) (@SetGerms.neg T 0 (germ S0)) = germ (\bigcup_i S i).
  rewrite hBeta hGamma;exact:holomorphic_stratification_germ hOld.
have [W [hW [hW0 hCover]]]:=@set_germ_difference_local_cover T 0 E S0 (\bigcup_i S i) hCovered.
pose O0:set X:=A `&` (U0 `&` W).
have hO0:@open T O0:=openI hA (openI hU0Open hW).
have hO00:O0 0 by split;last split.
have [Vnew [hVnew [hV0 [hVO0 hFinite]]]]:=hChoose O0 hO0 hO00 (fun x hx=>hx.1).
pose Snew:set X:=Vnew `&` D.
pose Gnew:set X:=Vnew `&` E.
have hVA:Vnew `<=` A by move=>x hx;exact:(hVO0 x hx).1.
have hGS:germ Snew = germ D:=@set_germ_neighbourhood_intersection T 0 Vnew D hVnew hV0.
have hGE:germ Gnew = germ E:=@set_germ_neighbourhood_intersection T 0 Vnew E hVnew hV0.
have hSplit:@SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) =
    @SetGerms.join T 0 (@SetGerms.meet T 0 gamma (@SetGerms.neg T 0 beta)) (germ Snew).
  rewrite hGS -hRegular;exact:set_germ_cut_difference_split hGA hABG.
have hNewLaws:@is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu.+1
    (ordinal_snoc V Vnew) (ordinal_snoc S Snew) (ordinal_snoc G Gnew).
  apply:(@holomorphic_stratification_append_regular R n alpha gamma beta m U0 S0 mu V S G
    Vnew Snew Gnew hOld hSplit).
  - split;first exact:hVnew.
    split;first exact:hV0.
    move=>x hx;exact:(hVO0 x hx).2.1.
  - exists d;split;first exact:hDM.
    have hFunctional:=functional_holomorphic_open_restriction hD hVnew hVA.
    have hSame:Vnew `&` (A `&` D) = Snew.
      apply/seteqP;split.
      + by move=>x [hx [_ hDx]];split.
      + move=>x [hx hDx];split;first exact:hx.
        split;[exact:hVA x hx|exact:hDx].
    by rewrite hSame in hFunctional.
  - exact:hFinite.
  - move=>x [hVx hDx] [hS0x|[i _ hSix]].
    + exact:(hDInside x hDx (hVA x hVx)).2 hS0x.
    + exact:hDE x hDx (hOldInside i x hSix).
  - move=>x [hVx hClosure].
    have hClosureD:@closure T D x:=@closureS T Snew D (fun x hx=>hx.2) x hClosure.
    have [hDx|hEx]:=hBoundary x (conj (hVA x hVx) hClosureD).
    + left;by split.
    + right;by split.
  - exact:finite_holomorphic_variety_open_restriction hE hVnew hVA.
  - by rewrite hGE.
  - move=>x [hVx hEx];exact:hCover x hEx (hVO0 x hVx).2.2.
exists Vnew,Snew,Gnew;split;first exact:hNewLaws.
move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
- move=>x hx;exact:hEH x (hOldInside j x hx).
- move=>x [hVx hDx];exact:(hDInside x hDx (hVA x hVx)).1.
Qed.
End RegularAssembly.
