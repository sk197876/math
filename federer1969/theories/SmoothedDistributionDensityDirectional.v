(** Federer (1969), 4.1.2, p. 347: the
    actual dual-valued density differentiates by applying
    the distribution to the negative kernel derivative.
    The scalar test quotient estimate is uniform over y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormedCurveDerivativeUP NormRegularity NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSpaceSealed SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothGlobalTranslationUP SmoothGlobalTranslationSealed SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed
  SmoothDifferenceQuotientJets SmoothDifferenceQuotientSeminorm SmoothTranslatedOrdinary
  TranslatedKernelTestUP TranslatedKernelTestCommonSupport DistributionTensorDualBound SmoothedDistributionDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionDensityDirectional.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable g:X->YD.
Hypothesis hg:is_smoothed_distribution_density B T ed g.


Variable v:X.
Variable theta:X->R.
Variable G:X->Hom X R^o.
Hypothesis hG:forall x,has_norm_differential N NS (fun _=>True) psi x (G x).
Hypothesis hTheta:forall x,G x v=theta x.
Hypothesis hThetaOff:forall x,r<N x ->theta x=0.
Variable CTest:X->Hom Y DT.
Hypothesis hCTest:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE theta CTest.
Variable q:X->YD.
Hypothesis hq:is_smoothed_distribution_density CTest T ed q.

(** Source for [smoothed_distribution_density_directional]: the
    actual kernel-density derivative implicit in the class-infinity
    assertion of Federer 4.1.2, p. 347. The
    derivative is in the full dual norm, including the
    zero direction and zero-dimensional source. *)
Theorem smoothed_distribution_density_directional z:
  punctured_norm_limit DN (fun t=>t^-1*:(g (z+t*:v)-g z)) (-q z).
Proof.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
have hL c:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS c.
pose P:=@SmoothDirectionalDerivative.operator R X R^o N NS hN hNS (fun _=>True)
  S sv hS DS hDS (-v).
pose hP:=@SmoothDirectionalDerivative.laws R X R^o N NS hN hNS (fun _=>True)
  S sv hS DS hDS (-v).
have[f hf]:=smooth_function_evaluation_surjective hS hPsi.
have hF x:sv f x=psi x:=hf x Logic.I.
have hRawFunction:sv f=psi by apply:funext=>x; exact:hF.
have hRaw x:has_norm_differential N NS (fun _=>True) (sv f) x (G x).
  rewrite hRawFunction; exact:hG.
have hPValue x:sv (P (L (-z) f)) x= -theta (x-z).
  have h:=@smooth_translated_ordinary_evaluation R X R^o N NS hN hNS S sv DS hDS
    L hL (-v) P hP f G hRaw (-z) x.
  have hNeg:G (x-z) (-v)= -G (x-z) v.
    exact:(linearN (hom_as_linear (G (x-z))) v).
  by rewrite h hNeg hTheta.
have hSvSub (a b:S) x:sv (a-b) x=sv a x-sv b x.
  exact:(congr1 (fun F:X->R^o=>F x)
    (linearB (hom_as_linear (smooth_function_values_hom hS)) a b)).
have hSvScale c (a:S) x:sv (c*:a) x=c*sv a x.
  exact:(congr1 (fun F:X->R^o=>F x)
    (linearZ_LR (hom_as_linear (smooth_function_values_hom hS)) c a)).
have hTvSub (a b:DT) x:smooth_test_value hE (a-b) x=
    smooth_test_value hE a x-smooth_test_value hE b x.
  exact:(congr1 (fun F:X->Y=>F x)
    (linearB (hom_as_linear (smooth_test_values_hom hE)) a b)).
have hTvAdd (a b:DT) x:smooth_test_value hE (a+b) x=
    smooth_test_value hE a x+smooth_test_value hE b x.
  exact:(congr1 (fun F:X->Y=>F x)
    (linearD (hom_as_linear (smooth_test_values_hom hE)) a b)).
have hTvScale c (a:DT) x:smooth_test_value hE (c*:a) x=c*:smooth_test_value hE a x.
  exact:(congr1 (fun F:X->Y=>F x)
    (linearZ_LR (hom_as_linear (smooth_test_values_hom hE)) c a)).
have hEdSub (a b:YD) y:ed (a-b) y=ed a y-ed b y.
  exact:(congr1 (fun F:Hom Y R^o=>F y) (linearB (hom_as_linear ed) a b)).
move=>eta hEta.
have[C0 hCommon]:=@translated_kernel_test_common_support R n Y NY hNY E ev hE psi r B hOff hB z.
have[C1 hThetaCommon]:=@translated_kernel_test_common_support R n Y NY hNY E ev hE theta r CTest hThetaOff hCTest z.
pose C:=smooth_compact_union C0 C1.
have hZero:N 0<=1 by rewrite (real_seminorm_zero hN.1); exact:ler01.
have hB0 y:smooth_fixed_support_subspace hE C (smooth_test_inclusion hE (B z y)).
  have h:=hCommon 0 hZero y; rewrite addr0 in h.
  move=>x hx; left; exact:h x hx.
have hC0 y:smooth_fixed_support_subspace hE C (smooth_test_inclusion hE (CTest z y)).
  have h:=hThetaCommon 0 hZero y; rewrite addr0 in h.
  move=>x hx; right; exact:h x hx.
have[i [M hBound]]:=@distribution_tensor_dual_bound R X Y N NY hN hNY E ev hE D hD
  T hT YD ed DN hYD hFull C.
have hM:(0<=(M%:R:R)):=ler0n R M.
have hDen:0<(M%:R:R)+1 by lra.
have hSmall:0<eta/(M%:R+1) by rewrite divr_gt0.
have[d [hd hEstimate]]:=@smooth_difference_quotient_seminorm_limit R X R^o N NS hN hNS
  S sv hS DS hDS (-v) P hP L hL (L (-z) f) C i (eta/(M%:R+1)) hSmall.
have hNv:0<=N v:=real_seminorm_nonnegative hN.1 v.
have hV:0<N v+1 by lra.
have hVInv:0<1/(N v+1) by rewrite divr_gt0.
exists (Num.min d (1/(N v+1))); split; first by rewrite lt_min hd hVInv.
move=>t /andP [ht0 htSmall].
have /andP [htd htV]: (`|t|<d) && (`|t|<1/(N v+1)) by move:htSmall; rewrite lt_min.
have ht:0<`|t|<d by rewrite ht0 htd.
have hTv:N (t*:v)<=1.
  rewrite (real_seminorm_scale hN.1).
  have hProduct:`|t|*(N v+1)<1 by move:htV; rewrite ltr_pdivlMr.
  have hNt:=normr_ge0 t; nra.
pose s:=@smooth_difference_quotient_error R X S (-v) P L t (L (-z) f).
pose F y:=t^-1*:(B (z+t*:v) y-B z y)+CTest z y.
have hB1 y:smooth_fixed_support_subspace hE C
    (smooth_test_inclusion hE (B (z+t*:v) y)).
  move=>x hx; left; exact:(hCommon (t*:v) hTv y x hx).
have hSupport y:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE (F y)) `<=` smooth_compact_carrier C.
  change (smooth_fixed_support_subspace hE C (smooth_test_inclusion hE (F y))).
  have hInc:smooth_test_inclusion hE (F y)=
      t^-1*:(smooth_test_inclusion hE (B (z+t*:v) y)-smooth_test_inclusion hE (B z y))+
      smooth_test_inclusion hE (CTest z y).
    by rewrite /F linearD linearZ linearB.
  rewrite hInc.
  have hDiff:=@subspace_sub R E (smooth_fixed_support_subspace hE C) _ _ (hB1 y) (hB0 y).
  have hScale:=@subspace_scale R E (smooth_fixed_support_subspace hE C) t^-1 _ hDiff.
  exact:(@subspace_add R E (smooth_fixed_support_subspace hE C) _ _ hScale (hC0 y)).
have hScalar x:sv s x=t^-1*(psi (x-(z+t*:v))-psi (x-z))+theta (x-z).
  rewrite /s /smooth_difference_quotient_error hSvSub hSvScale hSvSub !hL !hF hPValue opprK.
  have hShift:x+t*:(-v)+-z=x-(z+t*:v).
    by rewrite scalerN opprD !addrA addrAC.
  by rewrite hShift.
have hValue y x:smooth_test_value hE (F y) x=sv s x*:y.
  rewrite /F hTvAdd hTvScale hTvSub !hB hCTest hScalar.
  by rewrite -scalerBl scalerA -scalerDl.
have hPair y:ed (t^-1*:(g (z+t*:v)-g z)+q z) y=T (F y).
  have hEval:ed (t^-1*:(g (z+t*:v)-g z)+q z) y=
      t^-1*(ed (g (z+t*:v)-g z) y)+ed (q z) y.
    exact:(congr1 (fun A:Hom Y R^o=>A y)
      (hom_linear ed t^-1 (g (z+t*:v)-g z) (q z))).
  by rewrite hEval hEdSub !hg hq /F linearD linearZ /= linearB.
have hDual:=@hBound S sv DS hDS s (t^-1*:(g (z+t*:v)-g z)+q z) F hSupport hValue hPair.
have hNu:=hEstimate t ht.
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hDS C i) s.
have hStrict:(M%:R+1)*smooth_function_derivative_seminorm hDS C i s<
    (M%:R+1)*(eta/(M%:R+1)).
  by rewrite ltr_pM2l.
have hEq:(M%:R+1)*(eta/(M%:R+1))=eta by rewrite mulrC divfK // gt_eqF.
rewrite hEq in hStrict.
rewrite opprK; apply:le_lt_trans hDual _; nra.
Qed.
End SmoothedDistributionDensityDirectional.
