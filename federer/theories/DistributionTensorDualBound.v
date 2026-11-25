(** Federer (1969), 4.1.2, pp. 347-348:
    one original finite-order distribution bound controls
    the actual dual norm of all scalar kernel
    remainders multiplied by arbitrary vectors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP
  ContinuousDualUP RealFunctionalNormUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  DistributionSupportedBound SmoothScalarVectorSeminormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionTensorDualBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable hFull:forall x,(fun _=>True) x ->norm_domain_interior NX (fun _=>True) x.

(** Source for [distribution_tensor_dual_bound]: the original
    same-compact distribution estimate of 4.1.1, p. 345,
    gives a uniform dual-norm estimate for the
    kernel remainders in Federer 4.1.2, p. 347. *)
Theorem distribution_tensor_dual_bound (K:smooth_compact_set hNX (fun _=>True)):
  exists i M:nat,forall (S:lmodType R) (sv:S->X->R^o)
    (DS:forall j,X->Hom S (@ContinuousMultilinear.space R j X R^o NX
      (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)))
    (hDS:@is_smooth_function_derivatives R X R^o NX (fun t:R^o=>`|t|)
      hNX (@scalar_absolute_value_norm R) (fun _=>True) S sv DS)
    (s:S) (a:YD) (F:Y->DT),
    (forall y,@smooth_function_support R X Y NX hNX (fun _=>True) E ev
      (smooth_test_inclusion hE (F y)) `<=` smooth_compact_carrier K) ->
    (forall y x,smooth_test_value hE (F y) x=sv s x*:y) ->
    (forall y,ed a y=T (F y)) ->
    DN a<=M%:R * smooth_function_derivative_seminorm hDS K i s.
Proof.
have[i [M hBound]]:=@distribution_supported_local_bound R X Y NX NY hNX hNY
  (fun _=>True) hFull E ev hE D hD T hT K.
exists i,M=>S sv DS hDS s a F hSupport hValue hPair.
apply:(real_functional_norm_least (continuous_dual_norm_laws hYD a)).
- exact:mulr_ge0 (ler0n R M)
    (smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hDS K i) s).
- move=>y.
  rewrite hom_as_linearE hPair.
  apply:le_trans (hBound (F y) (hSupport y)) _.
  have hSeminorm:=@smooth_scalar_vector_seminorm_bound R X Y NX NY hNX hNY
    S sv DS hDS E ev D hD s (smooth_test_inclusion hE (F y)) y K i (hValue y).
  have h:=ler_wpM2l (ler0n R M) hSeminorm.
  by rewrite mulrA in h.
Qed.
End DistributionTensorDualBound.
