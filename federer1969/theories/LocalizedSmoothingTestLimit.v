(** Federer (1969), 4.1.2, p. 347: the
    original smoothed evaluations T(Phi_epsilon*f) converge
    to T(f) for every actual test. Continuity of T
    and the original test-topology convergence suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP TestSmoothingConvergence
  TestCutoffExhaustionUP FiniteCoordinates SmoothCompactInteriorThickening SmoothCompactCutoffUP SmoothCompactCutoffSealed
  SmoothCutoffReplacement SmoothMultiplierUP SmoothMultiplierSealed
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity
  SmoothTestEvaluation SmoothFunctionSupport TestZeroExtensionUP TestZeroExtensionLaws
  EuclideanLebesgueDimensions SmoothingDilationNonzeroRadius CompactConvolutionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalizedSmoothingTestLimit.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) E ev).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.
Variable Q:R->Hom DT DT.
Hypothesis hQ:@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.



Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable A:lmodType R.
Variable av:A->X->Y.
Hypothesis hA:is_smooth_function_space hN hNY U av.
Variable DA:forall j,X->Hom A (Z j).
Hypothesis hDA:@is_smooth_function_derivatives R X Y N NY hN hNY U A av DA.
Local Notation TA := (smooth_test_space hA).
Local Notation SA := (smooth_test_opens hA hDA).
Variable S0:lmodType R.
Variable sv:S0->X->R^o.
Hypothesis hS0:is_smooth_function_space hN (@scalar_absolute_value_norm R) U sv.
Variable omega:nat->smooth_test_space hS0.
Hypothesis hOmega:@is_test_cutoff_exhaustion R X N hN U S0 sv hS0 omega.
Variable L:Hom TA DT.
Hypothesis hL:is_test_zero_extension U (fun _=>True) (smooth_test_value hA) (smooth_test_value hE) L.
Variable T:Hom TA R^o.
Hypothesis hT:open_family_continuous SA (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable M:nat->Hom E TA.
Hypothesis hM:forall j g x,U x ->smooth_test_value hA (M j g) x=
  smooth_test_value hS0 (omega j) x*:ev g x.

(** Source for [localized_smoothing_test_limit]: the joint large-j,
    small-positive-epsilon approximation in the last paragraph of
    Federer 4.1.2, p. 348. A single cutoff threshold and a
    single smoothing radius work simultaneously for every later index. *)
Theorem localized_smoothing_test_limit f eta:0<eta ->
  exists v:nat,exists d:R,0<d /\ forall j,(v<=j)%N ->
    forall e:R,0<e ->e<d ->
      `|T (M j (inc (Q e (L f))))-T f|<eta.
Proof.
move=>hEta.
have[K hK]:=smooth_test_support_bound hA f.
have[r [hr [C [hKC hTube]]]]:=@smooth_compact_interior_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
have hFOff x:~smooth_compact_carrier K x ->ev (inc (L f)) x=0.
  have hExt:=@test_zero_extension_preserves_compact_bound R X Y N NY hN hNY U (fun _=>True)
    (fun _ _=>Logic.I) A E av ev hA hE L hL K f hK.
  exact:(smooth_function_compact_support_iff hE
    (@Build_smooth_compact_set R X N hN (fun _=>True) (smooth_compact_carrier K)
      (fun _ _=>Logic.I) (smooth_compact_is_compact K)) (inc (L f))).1 hExt x.
pose chi:=@SmoothCompactCutoff.value R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) U C hU.
pose hChi:=@SmoothCompactCutoff.laws R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) U C hU.
have[W [hW [hCW hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
pose Cut:=@smooth_cutoff_replacement R X Y N NY hN hNY n (@coordinate_basis R n)
  (@coordinate_basisP R n) U hU A av hA C.
pose rho:=@SmoothRestriction.operator R X Y N NY hN hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A E av ev hA hE.
pose hRho:=@SmoothRestriction.laws R X Y N NY hN hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A E av ev hA hE.
have hCutValue a x (hx:U x):smooth_test_value hA (Cut a) x=chi x*:av a x.
  rewrite /Cut /smooth_test_value smooth_cutoff_replacement_evaluation.
  exact:(@SmoothMultiplier.laws R X Y N NY hN hNY U A av hA chi
    (@smooth_cutoff_replacement_scalar_class R X N hN n
      (@coordinate_basis R n) (@coordinate_basisP R n) U hU C) a x hx).
have hBase:Cut (rho (inc (L f)))=f.
  apply:(smooth_test_values_extensional hA)=>x hx.
  rewrite hCutValue // (@hRho (inc (L f)) x hx).
  change (chi x*:smooth_test_value hE (L f) x=smooth_test_value hA f x).
  rewrite (@test_zero_extension_original R X Y TA DT U (fun _=>True)
    (smooth_test_value hA) (smooth_test_value hE) L hL f x hx).
  case:(pselect (smooth_compact_carrier C x))=>hCx.
  - have h1:chi x = 1:=hOne x (hCW x hCx).
    by rewrite h1 scale1r.
  - have hKx:~smooth_compact_carrier K x by move=>hkx; exact:hCx (hKC x hkx).
    have hZero: smooth_test_value hA f x=0:=
      (smooth_function_compact_support_iff hA K (smooth_test_inclusion hA f)).1 hK x hKx.
    by rewrite hZero scaler0.
have hRC:=@smooth_restriction_continuous R X Y N NY hN hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A E av ev DA D hDA hD rho hRho.
have hCC:=@smooth_cutoff_replacement_continuous R X Y N NY hN hNY n (@coordinate_basis R n)
  (@coordinate_basisP R n) U hU A av hA DA hDA C.
pose F:=hom_comp T (hom_comp Cut rho).
have hFC:open_family_continuous (smooth_function_opens hD)
    (norm_open_family (@scalar_absolute_value_norm R)) F.
  apply:(@open_family_continuous_compose E TA R^o (smooth_function_opens hD) SA
    (norm_open_family (@scalar_absolute_value_norm R)) (hom_comp Cut rho) T _ hT).
  exact:(@open_family_continuous_compose E A TA (smooth_function_opens hD)
    (smooth_function_opens hDA) SA rho Cut hRC hCC).
pose V:set R^o:=[set a:real_norm_metric_space (@scalar_absolute_value_norm R)|
  mdist (T f:real_norm_metric_space (@scalar_absolute_value_norm R)) a<eta].
have hV:norm_open_family (@scalar_absolute_value_norm R) V.
  exact:(@metric_open_ball_open R (real_norm_metric_space (@scalar_absolute_value_norm R)) (T f) eta).
have hPre:=@hFC V hV.
have hPoint:V (F (inc (L f))).
  have hEqual:F (inc (L f))=T f.
    change (T (Cut (rho (inc (L f))))=T f).
    by rewrite hBase.
  rewrite hEqual.
  change (is_true (mdist (T f:real_norm_metric_space (@scalar_absolute_value_norm R))
    (T f:real_norm_metric_space (@scalar_absolute_value_norm R))<eta)).
  by rewrite mdistxx.
have[d [hd hBound]]:=@smooth_smoothing_neighbourhood_limit R n Y NY hNY hY hSep
  E ev hE D hD phi hPhi family hFamily P hP (inc (L f)) _ hPre hPoint.
have[v [hv hPlateau]]:=hOmega C.
exists v,(Num.min r d); split; first by rewrite lt_min hr hd.
move=>j hj e he; rewrite lt_min=>/andP[her hed].
have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
have hZero x:~smooth_compact_carrier C x ->ev (P e (inc (L f))) x=0.
  apply:(@compact_convolution_support_bound R X Y N NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (smooth_compact_carrier K) (smooth_compact_carrier C) e (family e)
    (ev (inc (L f))) (ev (P e (inc (L f)))) hOff _ hFOff (@hP e he (inc (L f))) x).
  move=>y z hz hyz; exact:(@hTube y z hz (le_trans hyz (ltW her))).
have hEqual:M j (inc (Q e (L f)))=Cut (rho (P e (inc (L f)))).
  apply:(smooth_test_values_extensional hA)=>x hx.
  rewrite hM // hCutValue // (@hRho (P e (inc (L f))) x hx) (@hQ e he (L f)).
  case:(pselect (smooth_compact_carrier C x))=>hCx.
  - have h1:chi x = 1:=hOne x (hCW x hCx).
    by rewrite (@hPlateau j hj x hCx) h1.
  - by rewrite (hZero x hCx) !scaler0.
rewrite hEqual.
have h:=hBound e he hed.
change (is_true (`|T f-F (P e (inc (L f)))|<eta)) in h.
rewrite (real_seminorm_subtract (@scalar_absolute_value_norm R).1) in h.
exact h.
Qed.
End LocalizedSmoothingTestLimit.
