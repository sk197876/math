(** Federer (1969), 4.1.3, p. 348: the actual
    smoothing of every test lies in the closure of the
    canonical tensor image. The original fine Borel sums
    supply the approximants, with one common compact support
    and every required derivative seminorm estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormOpenDomainLaws ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothCompactThickening SmoothFunctionSpaceUP SmoothFunctionSpaceSealed
  SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed SmoothFunctionTopology
  SmoothGlobalTranslationUP SmoothGlobalTranslationSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  LinearSubspaceRepresentationUP SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothSmoothingFamilyUP TestSmoothingFamilyUP
  TranslatedKernelTestUP TranslatedKernelTestSealed TestTensorMapUP TranslatedSeparatedTestImage
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext MeasureUP
  TensorKernelApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TensorSmoothingClosure.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hNS hNS (fun _=>True) av.
Local Notation D1 := (smooth_test_space hA).
Variable gamma:D1.
Local Notation phi := (fun x:X=>\prod_i smooth_test_value hA gamma (x i)).
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y N NY hN hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Variable T W:lmodType R.
Variable muT:{dffun forall i:'I_n,D1}->T.
Variable nuT:T->Y->W.
Variable F:Hom W DT.
Hypothesis hF:is_test_tensor_map hA hE muT nuT F.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.
Variable Q:R->Hom DT DT.
Hypothesis hQ:@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.

(** Source for [tensor_smoothing_in_image_closure]: each actual
    smoothed test is approached by the original finite sums
    in the canonical tensor image, Federer 4.1.3, p. 348. *)
Theorem tensor_smoothing_in_image_closure (f:DT) e:
  0<e ->forall V,smooth_test_opens hE hD V ->V (Q e f) ->
    exists w:W,V (F w).
Proof.
move=>he V hV hPoint.
pose psi:=family e.
have hPsi:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
have[s hs]:=smooth_function_evaluation_surjective hS hPsi.
have hPsiValue x:sv s x=psi x:=hs x I.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
pose hL:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS.
pose B:=@TranslatedKernelTest.value R n Y NY hNY E ev hE psi hPsi e hOff.
pose hB:=@TranslatedKernelTest.laws R n Y NY hNY E ev hE psi hPsi e hOff.
have[K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
have hFOff x:~smooth_compact_carrier K x ->ev (inc f) x=0.
  exact:(smooth_function_compact_support_iff hE K _).1 hK x.
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hFinite:=@euclidean_distribution_measure_compact_finite R n
  (smooth_compact_carrier K) (smooth_compact_is_compact K).
have hNonnegative:=measure_nonnegative hm (smooth_compact_carrier K).
have hFin:mu (smooth_compact_carrier K) \is a fin_num by rewrite ge0_fin_numE.
pose b:=fine (mu (smooth_compact_carrier K)).
have hMass:mu (smooth_compact_carrier K)=b%:E by rewrite /b fineK.
have[C [_ hThick]]:=@smooth_compact_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) K e (ltW he).
have hImage z y:exists w:W,F w=B z y.
  exact:(@translated_separated_test_in_tensor_image R n A av hA gamma family hFamily
    Y NY hNY E ev hE T W muT nuT F hF e he B hB z y).
exact:(@tensor_kernel_approximation_neighbourhood R n Y NY hNY hY
  S sv hS DS hDS s psi hPsiValue e hOff E ev hE D hD
  (inc f) (P e (inc f)) (@hP e he (inc f)) K hFOff b hMass L hL B hB C hThick
  W F hImage (Q e f) (@hQ e he f) V hV hPoint).
Qed.
End TensorSmoothingClosure.
