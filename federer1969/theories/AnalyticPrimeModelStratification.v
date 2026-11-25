(** Federer (1969), corrected 3.4.8(11), pp. 327, 334–335:
    complete the original prime-model induction case.
    The actual exceptional cut has smaller dimension;
    the original component homeomorphisms and prepared
    equations give a finite-component regular neighbourhood.
    Exact local representatives supply every corrected
    boundary law, retaining the original analytic representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology NormFiniteLinearBound NormAnalyticUP NormAnalyticLinear NormAnalyticOperations
  NormAnalyticScalarProducts AnalyticGermRepresentatives AnalyticGermNeighbourhood AnalyticGermUP AnalyticGermRing
  OrthogonalGroupTopology SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermLocality
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyRestriction AnalyticVarietyGermUP IdealVarietyGermSealed
  GermVanishingSealed GermVanishingMonotonicity AnalyticDepthSealed AnalyticRotatedGermIdeal
  CommutativeIdealUP AnalyticReductionActual AnalyticPrefixCoordinatesSealed AnalyticPrimeLocalModelUP
  AnalyticPrimeModelExceptionalCut AnalyticFiniteStratificationUP AnalyticStratificationInductionUP
  AnalyticStratificationLowerLocal AnalyticStratificationExceptionalInduction AnalyticStratificationRegularAssembly
  AnalyticVarietyCutLocalData FunctionalAnalyticSubmanifoldUP FunctionalAnalyticOpenRestriction
  FunctionalAnalyticNonzeroCut AnalyticRestrictedProjectionComponents AnalyticPreparedNeighbourhoodChoice
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
Hypothesis hInduction:forall d,(d<m.+1)%N ->analytic_stratification_at_bound R d.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m.+1).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation hON:=(@euclidean_coordinate_orthonormal_family R n).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set A.
Variable g:@orthogonal_group R X B hB n e he.
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m.+1).
Variable U:set Y.
Variable delta:@analytic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m.+1)->'I_k->@analytic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m.+1)->@analytic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set A.
Variable hK:is_finitely_generated_commutative_ideal K.
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m.+1 hMN).
Local Notation alpha:=(@IdealVarietyGerm.value R X NX hNX 0 Ig hIg).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_prime_model_stratification_from_induction]:
    every corrected conclusion of the original
    n>m>0 prime-model case in 3.4.8(11),
    pp. 334–335. The original model comes from
    proved (10); the only induction input is
    the simultaneous result at strictly smaller depths. *)
Theorem analytic_prime_model_stratification_from_induction (U_H H U0 S0:set X):
  is_prime_commutative_ideal I ->
  @is_analytic_prime_local_model R n m.+1 hMN e he omega P Ig hIg k first U delta b f Z K hK ->
  Ig = ideal alpha ->
  (forall j:'I_n,(m.+1<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  U_H 0 ->@is_finite_analytic_variety R X NX hNX U_H H ->germ H = alpha ->
  U0 0 ->@is_finite_analytic_variety R X NX hNX U0 S0 ->~set_germ_subset alpha (germ S0) ->
  exists mu,exists V S G:'I_mu->set X,
    @is_analytic_finite_stratification R n alpha (germ S0) m.+1 U0 S0 mu V S G /\
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
case:hFields=>hFAnalytic hFields.
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
have hBeta:@is_analytic_variety_germ R X NX hNX 0 (germ S0).
  exists U0,S0;split;first exact:hU00.
  by split.
have [chi [L [hL [hGenerated [hIL [hLJ hData]]]]]]:=
  @analytic_prime_model_exceptional_cut R n m.+1 hMN e he omega hON hDual I g hIg
    k first U delta b f Z K hK (germ S0) hPrime (ltn0Sn m) hModel hRecovered
    hBeta hNotContained hTail.
pose gamma:=@IdealVarietyGerm.value R X NX hNX 0 L hL.
have [hGammaAlpha [hSigmaGamma [hCut [hDrop [hRegular hSplit]]]]]:=hData.
pose D:set X:=[set x|Z x /\vy chi (P x)<>0].
have [W [hW0 [_ [hW hChiW]]]]:=analytic_germ_open_representative (analytic_representative_analytic chi).
pose Q:set Y:=U `&` W.
have hQ:@open TY Q:=openI hUOpen hW.
have hQ0:Q 0 by split.
have hQInterior y (hy:Q y):norm_domain_interior NY Q y.
  have hOpen:=hQ;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY Q y).2 (hOpen y hy).
have hChiQ:=@norm_analytic_open_restriction R Y R^o NY (fun z:R^o=>`|z|) hNY
  (@scalar_absolute_value_norm R) W Q (vy chi) (fun y hy=>hy.2) hQInterior hChiW.
have hDeltaQ:=@norm_analytic_open_restriction R Y R^o NY (fun z:R^o=>`|z|) hNY
  (@scalar_absolute_value_norm R) U Q (vy delta) (fun y hy=>hy.1) hQInterior hDeltaU.
have hProduct:=norm_analytic_scalar_product hChiQ hDeltaQ.
have hPBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY n e he P.
have hP:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hPBound.
have hRange x (hx:Z x):U (P x) /\vy delta (P x)!=0.
  have h:=((hZEquation x).1 hx);split;[exact:h.1|exact:h.2.2].
have hFibres y:finite_set [set x|Z x /\P x = y]:=(hFibresRaw y).1.
have hLowerBase (W0 L0:set Y) (hW00:W0 0)
    (hL0:@is_finite_analytic_variety R Y NY hNY W0 L0)
    (hNonemptyL0:@set_germ TY 0 L0<>@set_germ TY 0 set0)
    (hSmall:(@AnalyticDepth.value R Y (@euclidean_inner_product R m.+1)
      (@euclidean_inner_productP R m.+1) m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1)
      (dual_basis (@coordinate_basisP R m.+1))
      (@AnalyticSetIdeal.value R Y NY hNY (0%R:Y) (@set_germ TY (0%R:Y) L0))<m.+1)%N):
    exists O:set Y,@open TY O /\O 0 /\
      finite_set (@connected_component TY L0 @` (L0 `&` O)).
  exact:(@analytic_stratification_lower_local_components R m.+1 hInduction m.+1 W0 L0 hW00 hL0 hSmall).
have [r0 [hR0 [hBallQ hFiniteBase]]]:=@analytic_restricted_projection_components_from_lower_depth
  R n m P Z U Q (vy chi) (vy delta) hQ0 (fun y hy=>hy.1) hChiQ hDeltaU hP
  hRange hHomeomorphisms hFibres hLowerBase.
have hDSub:set_germ_subset (germ D) alpha.
  rewrite -hRegular;exact:set_germ_meet_subset_left.
have hVanish:Ig `<=` ideal (germ D).
  rewrite hRecovered;exact:analytic_set_ideal_antitone hDSub.
have hChoice:=@analytic_prepared_neighbourhood_choice R X B hB n e he hON omega hDual
  I g m.+1 hMN D r0 hPrime.1 hPrime.2.1 hTail hVanish hR0 hFiniteBase.
pose U1:set X:=U_H `&` (P @^-1` Q).
pose H1:set X:=U1 `&` H.
have hP0:P 0 = 0:=linear0 P.
have hPreQ:@open T (P @^-1` Q):=@open_comp T TY P Q (fun x _=>hP x) hQ.
have hU1:@open T U1:=openI hH.1 hPreQ.
have hU10:U1 0 by split;last by change (Q (P 0));rewrite hP0.
have hH1:=@finite_analytic_variety_open_restriction R X NX hNX U_H U1 H hH hU1 (fun x hx=>hx.1).
have hH1Germ:germ H1 = alpha.
  rewrite /H1 (@set_germ_neighbourhood_intersection T 0 U1 H hU1 hU10);exact:hHGerm.
have hU1Interior x (hx:U1 x):norm_domain_interior NX U1 x.
  have hOpen:=hU1;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U1 x).2 (hOpen x hx).
have hPAnalytic:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY U1 hU1Interior P hPBound.
pose phi:X->R^o:=fun x=>vy chi (P x)*vy delta (P x).
have hPhi:=@norm_analytic_compose_on R X Y R^o NX NY (fun z:R^o=>`|z|) hNX hNY
  (@scalar_absolute_value_norm R) U1 Q P (fun y=>vy chi y*vy delta y)
  (fun x hx=>hx.2) hPAnalytic hProduct.
have hCutLocal:gamma = @SetGerms.meet T 0 (germ H1) (germ [set x|phi x=0]).
  by rewrite hH1Germ.
have hRegularLocal:germ D = @SetGerms.meet T 0 (germ H1) (@SetGerms.neg T 0 gamma).
  by rewrite hH1Germ hRegular.
have hContainedLocal:set_germ_subset (@SetGerms.meet T 0 (germ H1) (germ S0)) gamma.
  by rewrite hH1Germ.
have [A0 [E0 [hA0 [hA00 [hA0U1 [hE0 [hE0Germ [hE0H1 [hDInside [hDE0 hBoundary]]]]]]]]]]:=
  @analytic_variety_cut_local_data R X NX hNX U1 H1 D S0 phi gamma hU10 hH1 hPhi
    hCutLocal hRegularLocal hContainedLocal.
have hE0Drop:germ E0 = germ set0 \/(depth (ideal (germ E0))<m.+1)%N by rewrite hE0Germ.
have [mu [V [S [G [hOld hOldInside]]]]]:=@analytic_exceptional_stratification_from_induction
  R m.+1 hInduction n A0 E0 U0 S0 hA00 hE0 hU00 hS0 hE0Drop.
rewrite hE0Germ in hOld.
have hA0Interior x (hx:A0 x):norm_domain_interior NX A0 x.
  have hOpen:=hA0;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX A0 x).2 (hOpen x hx).
have hA0Original:A0 `<=` [set x|U (P x)].
  move=>x hx;exact:(hA0U1 x hx).2.1.
have hZRestricted:=functional_analytic_open_restriction hModelFunctional hA0 hA0Original.
have hChiP:=@norm_analytic_compose_on R X Y R^o NX NY (fun z:R^o=>`|z|) hNX hNY
  (@scalar_absolute_value_norm R) A0 Q P (vy chi) (fun x hx=>(hA0U1 x hx).2)
  (@norm_bounded_linear_analytic R X Y NX NY hNX hNY A0 hA0Interior P hPBound) hChiQ.
have hFunctionalCut:=functional_analytic_nonzero_cut hZRestricted hChiP.
have hFunctional:@is_functional_analytic_submanifold R n m.+1 A0 (A0 `&` D).
  have hSame:[set x|(A0 `&` Z) x /\vy chi (P x)<>0] = A0 `&` D.
    apply/seteqP;split;[by move=>x [[hx hz] hn];split;last split|by move=>x [hx [hz hn]];split;first split].
  by rewrite hSame in hFunctionalCut.
have [Vnew [Snew [Gnew [hLaws hInside]]]]:=@analytic_stratification_regular_assembly R n
  alpha (germ S0) gamma m.+1 m.+1 A0 H E0 D U0 S0 mu V S G
  hA0 hA00 hU00 hS0.1 (erefl _) hE0Germ hGammaAlpha hSigmaGamma hRegular hE0
  hFunctional (leqnn m.+1) hE0Drop (fun x hx=>(hE0H1 x hx).2)
  (fun x hx hAx=>conj (hDInside x hx hAx).1.2 (hDInside x hx hAx).2)
  hDE0 hBoundary hOld hOldInside (fun W0 hW0 hW00 _=>@hChoice W0 hW0 hW00).
exists mu.+1,(ordinal_snoc V Vnew),(ordinal_snoc S Snew),(ordinal_snoc G Gnew).
by split.
Qed.
End PrimeStratification.
