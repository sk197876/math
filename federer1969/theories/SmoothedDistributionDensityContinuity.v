(** Federer (1969), 4.1.2, p. 347: the
    actual dual-valued kernel density is continuous in
    the full dual norm. A common compact support
    and scalar seminorm estimates give a bound uniform
    over all coefficient vectors y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormRegularity NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSpaceSealed SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothGlobalTranslationUP SmoothGlobalTranslationSealed SmoothTranslationSeminormContinuity
  TranslatedKernelTestUP TranslatedKernelTestCommonSupport DistributionTensorDualBound SmoothedDistributionDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionDensityContinuity.
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

(** Source for [smoothed_distribution_density_continuous]: the
    continuity part of g_epsilon belonging to class infinity
    in Federer 4.1.2, p. 347. This is norm
    continuity, with no separability assumption on Y*. *)
Theorem smoothed_distribution_density_continuous:
  norm_class_zero N DN (fun _=>True) g.
Proof.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
have hL c:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS c.
have[f hf]:=smooth_function_evaluation_surjective hS hPsi.
have hF x:sv f x=psi x:=hf x Logic.I.
have hSvSub (a b:S) x:sv (a-b) x=sv a x-sv b x.
  exact:(congr1 (fun F:X->R^o=>F x)
    (linearB (hom_as_linear (smooth_function_values_hom hS)) a b)).
have hTvSub (a b:DT) x:smooth_test_value hE (a-b) x=
    smooth_test_value hE a x-smooth_test_value hE b x.
  exact:(congr1 (fun F:X->Y=>F x)
    (linearB (hom_as_linear (smooth_test_values_hom hE)) a b)).
move=>z _; split; first exact:norm_full_domain_interior N z.
move=>eta hEta.
have[C hCommon]:=@translated_kernel_test_common_support R n Y NY hNY E ev hE psi r B hOff hB z.
have hBase y:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE (B z y)) `<=` smooth_compact_carrier C.
  have hZero:N 0<=1 by rewrite (real_seminorm_zero hN.1); exact:ler01.
  have h:=hCommon 0 hZero y.
  by rewrite addr0 in h.
have[i [M hBound]]:=@distribution_tensor_dual_bound R X Y N NY hN hNY E ev hE D hD
  T hT YD ed DN hYD hFull C.
have hM:(0<=(M%:R:R)):=ler0n R M.
have hDen:0<(M%:R:R)+1 by lra.
have hSmall:0<eta/(M%:R+1) by rewrite divr_gt0.
have[d [hd hEstimate]]:=@smooth_translation_seminorm_continuity R X R^o N NS hN hNS
  S sv DS hDS L hL (L (-z) f) C i (eta/(M%:R+1)) hSmall.
exists (Num.min 1 d); split; first by rewrite lt_min ltr01 hd.
move=>h _; rewrite lt_min=>/andP [hh1 hhd].
pose s:=L (-h) (L (-z) f)-L (-z) f.
pose F y:=B (z+h) y-B z y.
have hSupport y:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE (F y)) `<=` smooth_compact_carrier C.
  change (smooth_fixed_support_subspace hE C (smooth_test_inclusion hE (F y))).
  rewrite /F linearB /=.
  exact:(@subspace_sub R E (smooth_fixed_support_subspace hE C)
    (smooth_test_inclusion hE (B (z+h) y)) (smooth_test_inclusion hE (B z y))
    (hCommon h (ltW hh1) y) (hBase y)).
have hValue y x:smooth_test_value hE (F y) x=sv s x*:y.
  rewrite /F hTvSub !hB -scalerBl /s hSvSub !hL !hF.
  have hShift:x+-h+-z=x-(z+h) by rewrite opprD !addrA addrAC.
  by rewrite hShift.
have hPair y:ed (g (z+h)-g z) y=T (F y).
  have hEval:ed (g (z+h)-g z) y=ed (g (z+h)) y-ed (g z) y.
    exact:(congr1 (fun A:Hom Y R^o=>A y)
      (linearB (hom_as_linear ed) (g (z+h)) (g z))).
  by rewrite hEval !hg /F linearB.
have hDual:=@hBound S sv DS hDS s (g (z+h)-g z) F hSupport hValue hPair.
have hnh:N (-h)<d by rewrite (real_seminorm_negate hN.1).
have hNu:=hEstimate (-h) hnh.
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hDS C i) s.
have hStrict:(M%:R+1)*smooth_function_derivative_seminorm hDS C i s<
    (M%:R+1)*(eta/(M%:R+1)).
  by rewrite ltr_pM2l.
have hEq:(M%:R+1)*(eta/(M%:R+1))=eta by rewrite mulrC divfK // gt_eqF.
rewrite hEq in hStrict.
apply:le_lt_trans hDual _; nra.
Qed.
End SmoothedDistributionDensityContinuity.
