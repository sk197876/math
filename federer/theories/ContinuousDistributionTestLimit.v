(** Federer (1969), 4.1.4, pp. 348–349, using 4.1.2, p. 347: the
    original smoothed evaluations T(Phi_epsilon*f) converge
    to T(f) for every actual test. Continuity of T
    and the original test-topology convergence suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP ContinuousTestSmoothingConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ContinuousDistributionTestLimit.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
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


Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) T.

(** Source for [continuous_distribution_smoothing_test_limit]: the pointwise
    test-evaluation limit in the displayed weak convergence
    statement of Federer 4.1.2, p. 347.
    The smoothing parameter tends to zero through positive values. *)
Theorem continuous_distribution_smoothing_test_limit f eta:
  0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    `|T (Q e f)-T f|<eta.
Proof.
move=>hEta.
pose hR:=@scalar_absolute_value_norm R.
pose V:set R^o:=[set a:real_norm_metric_space hR|mdist (T f:real_norm_metric_space hR) a<eta].
have hV:norm_open_family hR V.
  exact:(@metric_open_ball_open R (real_norm_metric_space hR) (T f) eta).
have hPre:=@hT V hV.
have hCenter:V (T f).
  change (is_true (mdist (T f:real_norm_metric_space hR) (T f:real_norm_metric_space hR)<eta)).
  by rewrite mdistxx.
have[d [hd hBound]]:=@continuous_test_smoothing_neighbourhood_limit R n Y NY hNY hY
  E ev hE D hD phi hPhi family hFamily P hP Q hQ f _ hPre hCenter.
exists d; split=>// e he hSmall.
have h:=hBound e he hSmall.
change (is_true (`|T f-T (Q e f)|<eta)) in h.
by rewrite (real_seminorm_subtract hR.1) in h.
Qed.
End ContinuousDistributionTestLimit.
