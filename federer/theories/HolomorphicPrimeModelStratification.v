(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 334–335:
    complete the original prime-model induction case.
    The actual exceptional cut has smaller dimension;
    the proved real-case component theorem gives the final
    finite-component regular neighbourhood, as permitted in 3.4.12.
    Exact local representatives supply every corrected
    boundary law, retaining the original holomorphic representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import SetGermExistence StandardHermitianBasisValues FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology NormFiniteLinearBound HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus
  HolomorphicProduct HolomorphicGermRepresentatives HolomorphicGermNeighbourhood HolomorphicGermUP HolomorphicGermRing
  OrthogonalGroupTopology SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermLocality
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRestriction HolomorphicVarietyGermUP HolomorphicIdealVarietyGermSealed
  HolomorphicGermVanishingSealed HolomorphicGermVanishingMonotonicity HolomorphicDepthSealed HolomorphicRotatedGermIdeal
  CommutativeIdealUP HolomorphicReductionActual FieldPrefixCoordinatesSealed HolomorphicPrimeLocalModelUP
  HolomorphicPrimeModelExceptionalCut HolomorphicFiniteStratificationUP HolomorphicStratificationInductionUP
  HolomorphicStratificationExceptionalInduction HolomorphicStratificationRegularAssembly
  HolomorphicVarietyCutLocalData FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicOpenRestriction
  FunctionalHolomorphicNonzeroCut HolomorphicDifferenceFiniteNeighbourhood HolomorphicDifferenceGermFiniteNeighbourhood
  InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrimeStratification.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m.+1<=n)%N.
Hypothesis hInduction:forall d,(d<m.+1)%N ->holomorphic_stratification_at_bound R d.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m.+1).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation NY:=(@holomorphic_coordinate_norm R m.+1).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m.+1)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation hON:=(@standard_hermitian_basis_orthonormal R n).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Variable I:set A.
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m.+1).
Variable U:set Y.
Variable delta:@holomorphic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m.+1)->'I_k->@holomorphic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m.+1)->@holomorphic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set A.
Variable hK:is_finitely_generated_commutative_ideal K.
Local Notation vy:=(@holomorphic_representative_value R Y NY hNY 0).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m.+1 hMN).
Local Notation alpha:=(@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_prime_model_stratification_from_induction]:
    every corrected conclusion of the original
    n>m>0 prime-model case in 3.4.12, p. 339, extending 3.4.8(11),
    pp. 334–335. The original model comes from
    proved (10); the only induction input is
    the simultaneous result at strictly smaller depths. *)
Theorem holomorphic_prime_model_stratification_from_induction (U_H H U0 S0:set X):
  is_prime_commutative_ideal I ->
  @is_holomorphic_prime_local_model R n m.+1 hMN e he omega P Ig hIg k first U delta b f Z K hK ->
  Ig = ideal alpha ->
  (forall j:'I_n,(m.+1<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g) ->
  U_H 0 ->@is_finite_holomorphic_variety R X NX hNX U_H H ->germ H = alpha ->
  U0 0 ->@is_finite_holomorphic_variety R X NX hNX U0 S0 ->~set_germ_subset alpha (germ S0) ->
  exists mu,exists V S G:'I_mu->set X,
    @is_holomorphic_finite_stratification R n alpha (germ S0) m.+1 U0 S0 mu V S G /\
    forall i,S i `<=` H.
Proof.
move=>hPrime hModel hRecovered hTail hUH0 hH hHGerm hU00 hS0 hNotContained.
have hFields:=hModel.
case:hFields=>hFirst hFields.
case:hFields=>hKPositive hFields.
case:hFields=>hU0 hFields.
case:hFields=>hUOpen hFields.
case:hFields=>hDeltaU hFields.
case:hFields=>hBCoefficients hFields.
case:hFields=>hFHolomorphic hFields.
case:hFields=>hBZero hFields.
case:hFields=>hFFormula hFields.
case:hFields=>hZEquation hFields.
case:hFields=>hDeltaOutside hFields.
case:hFields=>hFIdeal hFields.
case:hFields=>hKGenerated hFields.
case:hFields=>hModelVariety hFields.
case:hFields=>hFirstDifferential hFields.
case:hFields=>hModelFunctional hFields.
case:hFields=>hCompactFibres hFields.
case:hFields=>hFibresRaw hFields.
case:hFields=>hHomeomorphisms hFields.

have hDual i j:omega i (e j) = if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hBeta:@is_holomorphic_variety_germ R X NX hNX 0 (germ S0).
  exists U0,S0;split;first exact:hU00.
  by split.
have [chi [L [hL [hGenerated [hIL [hLJ hData]]]]]]:=
  @holomorphic_prime_model_exceptional_cut R n m.+1 hMN e he omega hON hDual I g hIg
    k first U delta b f Z K hK (germ S0) hPrime (ltn0Sn m) hModel hRecovered
    hBeta hNotContained hTail.
pose gamma:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 L hL.
have [hGammaAlpha [hSigmaGamma [hCut [hDrop [hRegular hSplit]]]]]:=hData.
pose D:set X:=[set x|Z x /\vy chi (P x)<>0].
have [W [hW0 [_ [hW hChiW]]]]:=holomorphic_germ_open_representative chi.
pose Q:set Y:=U `&` W.
have hQ:@open TY Q:=openI hUOpen hW.
have hQ0:Q 0 by split.
have hQInterior y (hy:Q y):@norm_domain_interior R YR NY Q y.
  have hOpen:=hQ;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R YR NY hNY Q y).2 (hOpen y hy).
have hChiQ:=@holomorphic_open_restriction R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) W Q (vy chi) (fun y hy=>hy.2) hQInterior hChiW.
have hDeltaQ:=@holomorphic_open_restriction R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) U Q (vy delta) (fun y hy=>hy.1) hQInterior hDeltaU.
have hProduct:=holomorphic_product hChiQ hDeltaQ.
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (n+n) eR heR (complex_hom_real P).
have hP:=@norm_bounded_linear_continuous R XR YR NX NY hNX hNY (complex_hom_real P) hPBound.
have hRange x (hx:Z x):U (P x) /\vy delta (P x)!=0.
  have h:=((hZEquation x).1 hx);split;[exact:h.1|exact:h.2.2].
have hFibres y:finite_set [set x|Z x /\P x = y]:=(hFibresRaw y).1.
pose U1:set X:=U_H `&` (P @^-1` Q).
pose H1:set X:=U1 `&` H.
have hP0:P 0 = 0:=linear0 P.
have hPreQ:@open T (P @^-1` Q):=@open_comp T TY P Q (fun x _=>hP x) hQ.
have hU1:@open T U1:=openI hH.1 hPreQ.
have hU10:U1 0 by split;last by change (Q (P 0));rewrite hP0.
have hH1:=@finite_holomorphic_variety_open_restriction R X NX hNX U_H U1 H hH hU1 (fun x hx=>hx.1).
have hH1Germ:germ H1 = alpha.
  rewrite /H1 (@set_germ_neighbourhood_intersection T 0 U1 H hU1 hU10);exact:hHGerm.
have hU1Interior x (hx:U1 x):@norm_domain_interior R XR NX U1 x.
  have hOpen:=hU1;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX U1 x).2 (hOpen x hx).
have hPHolomorphic:=@holomorphic_bounded_linear R X Y NX NY hNX hNY U1 P hU1Interior hPBound.
pose phi:X->(ComplexScalars.C R)^o:=fun x=>vy chi (P x)*vy delta (P x).
have hPhi:=@holomorphic_compose_on R X Y (ComplexScalars.C R)^o NX NY (@complex_modulus R) hNX hNY
  (@complex_modulus_real_norm R) U1 Q P (fun y=>vy chi y*vy delta y)
  (fun x hx=>hx.2) hPHolomorphic hProduct.
have hCutLocal:gamma = @SetGerms.meet T 0 (germ H1) (germ [set x|phi x=0]).
  by rewrite hH1Germ.
have hRegularLocal:germ D = @SetGerms.meet T 0 (germ H1) (@SetGerms.neg T 0 gamma).
  by rewrite hH1Germ hRegular.
have hContainedLocal:set_germ_subset (@SetGerms.meet T 0 (germ H1) (germ S0)) gamma.
  by rewrite hH1Germ.
have [A0 [E0 [hA0 [hA00 [hA0U1 [hE0 [hE0Germ [hE0H1 [hDInside [hDE0 hBoundary]]]]]]]]]]:=
  @holomorphic_variety_cut_local_data R X NX hNX U1 H1 D S0 phi gamma hU10 hH1 hPhi
    hCutLocal hRegularLocal hContainedLocal.
have hE0Drop:germ E0 = germ set0 \/(depth (ideal (germ E0))<m.+1)%N by rewrite hE0Germ.
have [mu [V [S [G [hOld hOldInside]]]]]:=@holomorphic_exceptional_stratification_from_induction
  R m.+1 hInduction n A0 E0 U0 S0 hA00 hE0 hU00 hS0 hE0Drop.
rewrite hE0Germ in hOld.
have hA0Interior x (hx:A0 x):@norm_domain_interior R XR NX A0 x.
  have hOpen:=hA0;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX A0 x).2 (hOpen x hx).
have hA0Original:A0 `<=` [set x|U (P x)].
  move=>x hx;exact:(hA0U1 x hx).2.1.
have hZRestricted:=functional_holomorphic_open_restriction hModelFunctional hA0 hA0Original.
have hChiP:=@holomorphic_compose_on R X Y (ComplexScalars.C R)^o NX NY (@complex_modulus R) hNX hNY
  (@complex_modulus_real_norm R) A0 Q P (vy chi) (fun x hx=>(hA0U1 x hx).2)
  (@holomorphic_bounded_linear R X Y NX NY hNX hNY A0 P hA0Interior hPBound) hChiQ.
have hFunctionalCut:=functional_holomorphic_nonzero_cut hZRestricted hChiP.
have hFunctional:@is_functional_holomorphic_submanifold R n m.+1 A0 (A0 `&` D).
  have hSame:[set x|(A0 `&` Z) x /\vy chi (P x)<>0] = A0 `&` D.
    apply/seteqP;split;[by move=>x [[hx hz] hn];split;last split|by move=>x [hx [hz hn]];split;first split].
  by rewrite hSame in hFunctionalCut.

have hHVariety:@is_holomorphic_variety_germ R X NX hNX 0 (germ H).
  exists U_H,H;split;first exact:hUH0;by split.
have hEVariety:@is_holomorphic_variety_germ R X NX hNX 0 (germ E0).
  exists A0,E0;split;first exact:hA00;by split.
have hDifference:germ D = germ (H `\` E0).
  have hFormula:germ (H `\` E0) = @SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ E0)).
    by rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
      (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
  rewrite hFormula hHGerm hE0Germ;exact:esym hRegular.
have hChoice:=@holomorphic_difference_germ_finite_neighbourhood R n H E0 D hHVariety hEVariety hDifference.
have [Vnew [Snew [Gnew [hLaws hInside]]]]:=@holomorphic_stratification_regular_assembly R n
  alpha (germ S0) gamma m.+1 m.+1 A0 H E0 D U0 S0 mu V S G
  hA0 hA00 hU00 hS0.1 (erefl _) hE0Germ hGammaAlpha hSigmaGamma hRegular hE0
  hFunctional (leqnn m.+1) hE0Drop (fun x hx=>(hE0H1 x hx).2)
  (fun x hx hAx=>conj (hDInside x hx hAx).1.2 (hDInside x hx hAx).2)
  hDE0 hBoundary hOld hOldInside (fun W0 hW0 hW00 _=>@hChoice W0 hW0 hW00).
exists mu.+1,(ordinal_snoc V Vnew),(ordinal_snoc S Snew),(ordinal_snoc G Gnew).
by split.
Qed.
End PrimeStratification.
