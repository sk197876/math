(** Federer (1969), 4.1.2, p. 347: convergence
    in E with one common compact support gives
    positive-scale convergence in the literal final
    topology on D. All neighbourhoods are tested
    in one original fixed-support step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed LinearSubspaceRepresentationUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothSupportedPositiveLimit.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).

(** Source for [smooth_supported_positive_limit]: the exact
    common-support inference used for Phi_epsilon*f
    in Federer 4.1.2, p. 347.
    Joint vector continuity of the final test
    topology is neither assumed nor used. *)
Theorem smooth_supported_positive_limit (f:R->DT) (g:DT)
    (K:smooth_compact_set hNX U) r:
  0<r ->support (inc g) `<=` smooth_compact_carrier K ->
  (forall t:R,0<t ->t<r ->support (inc (f t)) `<=` smooth_compact_carrier K) ->
  (forall L:smooth_compact_set hNX U,forall i,forall eta:R,0<eta ->
    exists d:R,0<d /\ forall t:R,0<t ->t<d ->nu L i (inc (f t)-inc g)<eta) ->
  forall A,SO A ->A g ->exists d:R,0<d /\ forall t:R,0<t ->t<d ->A (f t).
Proof.
move=>hr hSupport hFamilySupport hSem A hA hg.
have hStepOpen:=((smooth_test_final_topology_laws hE hD).2 A).1 hA K.
have [gK hGK]:=subspace_representation_full (smooth_fixed_test_space_laws hE K) hSupport.
have hBase:smooth_test_step hE K gK=g.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hGK.
have hStepPoint:A (smooth_test_step hE K gK) by rewrite hBase.
have [[i L] [eta [hEta hBall]]]:=((smooth_test_step_topology_laws hE hD K).2 _).1 hStepOpen gK hStepPoint.
have [d [hd hBound]]:=hSem L i eta hEta.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t ht hSmall.
have hSmallR:t<r.
  apply:lt_le_trans hSmall _; by rewrite ge_min lexx.
have hSmallD:t<d.
  apply:lt_le_trans hSmall _; by rewrite ge_min lexx orbT.
have [fK hFK]:=subspace_representation_full (smooth_fixed_test_space_laws hE K)
  (@hFamilySupport t ht hSmallR).
have hPoint:smooth_test_step hE K fK=f t.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hFK.
rewrite -hPoint; apply:hBall.
change (nu L i (smooth_fixed_test_inclusion hE K (fK-gK))<eta).
have hDifference:smooth_fixed_test_inclusion hE K (fK-gK)=inc (f t)-inc g.
  have hCore:smooth_fixed_test_inclusion hE K (fK-gK)=
      smooth_fixed_test_inclusion hE K fK-smooth_fixed_test_inclusion hE K gK.
    by rewrite linearB.
  by rewrite hCore hFK hGK.
rewrite hDifference; exact:(hBound t ht hSmallD).
Qed.
End SmoothSupportedPositiveLimit.
