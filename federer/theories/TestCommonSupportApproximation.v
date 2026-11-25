(** Federer (1969), 4.1.3, p. 348: the finite sums of
    4.1.2 approach the convolution in its original test topology.
    This supporting neighbourhood lemma places the approximants
    in one actual compact step, without assuming joint vector
    continuity of the literal final topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestCommonSupportApproximation.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
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

(** Source for [test_common_support_approximation_neighbourhood]:
    same-compact seminorm approximation meets every literal test
    neighbourhood, the inference used for the tensor image in
    Federer 4.1.3, p. 348. *)
Theorem test_common_support_approximation_neighbourhood
    (H:set DT) (g:DT) (K:smooth_compact_set hNX U):
  support (inc g) `<=` smooth_compact_carrier K ->
  (forall L:smooth_compact_set hNX U,forall i,forall eta:R,0<eta ->
    exists h:DT,H h /\ support (inc h) `<=` smooth_compact_carrier K /\
      nu L i (inc h-inc g)<eta) ->
  forall A,SO A ->A g ->exists h:DT,H h /\ A h.
Proof.
move=>hSupport hApprox A hA hg.
have hStepOpen:=((smooth_test_final_topology_laws hE hD).2 A).1 hA K.
have[gK hGK]:=subspace_representation_full (smooth_fixed_test_space_laws hE K) hSupport.
have hBase:smooth_test_step hE K gK=g.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hGK.
have hStepPoint:A (smooth_test_step hE K gK) by rewrite hBase.
have[[i L] [eta [hEta hBall]]]:=((smooth_test_step_topology_laws hE hD K).2 _).1 hStepOpen gK hStepPoint.
have[h [hH [hSupportH hSmall]]]:=hApprox L i eta hEta.
have[hK hHK]:=subspace_representation_full (smooth_fixed_test_space_laws hE K) hSupportH.
have hPoint:smooth_test_step hE K hK=h.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hHK.
exists h; split=>//; rewrite -hPoint; apply:hBall.
change (nu L i (smooth_fixed_test_inclusion hE K (hK-gK))<eta).
have hDifference:smooth_fixed_test_inclusion hE K (hK-gK)=inc h-inc g.
  have hCore:smooth_fixed_test_inclusion hE K (hK-gK)=
      smooth_fixed_test_inclusion hE K hK-smooth_fixed_test_inclusion hE K gK.
    by rewrite linearB.
  by rewrite hCore hHK hGK.
by rewrite hDifference.
Qed.
End TestCommonSupportApproximation.
