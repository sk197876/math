(** Federer (1969), 4.1.1, p. 344: all
    members of a convergent weak E' sequence
    belong to one E'_K. The limit also
    belongs to that closed subset. The proof
    retains the original finite source and given norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP OpenFamilyConvergence WeakEvaluationTopologySealed WeakEvaluationConvergenceUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology FunctionalSupportUP
  ContinuousRealDual SmoothDualPointwiseBoundedSupport SmoothDualFixedSupportClosed RealOpenSequenceFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeakSequenceCommonSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation ED := (@continuous_real_dual_space R E EO hEO).
Local Notation e := (@continuous_real_dual_evaluation R E EO hEO).
Local Notation WO := (@continuous_real_dual_weak_opens R E EO hEO).
Local Notation support := (@smooth_functional_support R X Y NX hNX U E ev).

(** Source for [smooth_dual_weak_sequence_common_support]:
    every convergent weak sequence and its limit
    are supported in one compact K, the original
    sequence assertion of Federer 4.1.1,
    p. 344, with the printed E'_K
    closedness also applied to its limit. *)
Theorem smooth_dual_weak_sequence_common_support (S:nat->ED) (T:ED):
  open_family_converges WO (S @ \oo) T ->
  exists K:smooth_compact_set hNX U,
    (forall j,support (e (S j)) `<=` smooth_compact_carrier K) /\
    support (e T) `<=` smooth_compact_carrier K.
Proof.
move=>hCvg.
have hF:Filter (S @ \oo):=fmap_filter S (@filter_filter nat eventually eventually_filter).
have hWeak:=@WeakEvaluationTopology.convergence R E ED (fun A f=>e A f) (S @ \oo) hF T.
have hBound f:exists M:R,0<=M /\ forall j,`|e (S j) f|<=M.
  exact:(@real_open_convergent_sequence_bounded R (fun j=>e (S j) f) (e T f) ((hWeak.1 hCvg) f)).
have [K hK]:=@smooth_dual_pointwise_bounded_common_support R X Y NX NY hNX hNY d b hb U hU E ev hE
  D hD S hBound.
exists K; split; first exact hK.
case:(pselect (support (e T) `<=` smooth_compact_carrier K))=>// hNo.
pose A:set ED:=[set Q|~(support (e Q) `<=` smooth_compact_carrier K)].
have hOpen:WO A:=@smooth_dual_fixed_support_weakly_closed R X Y NX NY hNX hNY d b hb U hU E ev hE D hD K.
have [N _ hN]:=hCvg A hOpen hNo.
exact:False_ind _ (hN N (leqnn N) (hK N)).
Qed.
End WeakSequenceCommonSupport.
