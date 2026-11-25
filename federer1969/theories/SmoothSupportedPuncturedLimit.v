(** Federer (1969), 4.1.1, p. 346: convergence
    in E with one compact support bound implies
    convergence in D. The proof uses the exact
    final and fixed-step topology laws, without
    assuming D is a vector topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSubspaces SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SupportedPuncturedLimit.
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
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).

(** Source for [smooth_supported_punctured_limit]: a family
    supported in one compact K near zero and
    converging in every E seminorm tends to
    zero in D, supporting the Taylor assertion
    of Federer 4.1.1, p. 346. *)
Theorem smooth_supported_punctured_limit (f:R->DT) (K:smooth_compact_set hNX U) r:
  0<r ->
  (forall t,`|t|<r ->@smooth_function_support R X Y NX hNX U E ev (inc (f t))
    `<=` smooth_compact_carrier K) ->
  (forall L:smooth_compact_set hNX U,forall i,forall e:R,0<e ->exists d:R,0<d /\
    forall t,0<`|t|<d ->nu L i (inc (f t))<e) ->
  forall A,SO A ->A 0 ->exists d:R,0<d /\ forall t,0<`|t|<d ->A (f t).
Proof.
move=>hr hSupp hSem A hA hZero.
have hStepOpen:=((smooth_test_final_topology_laws hE hD).2 A).1 hA K.
have hStepZero:A (smooth_test_step hE K 0) by rewrite linear0.
have [[i L] [e [he hBall]]]:=((smooth_test_step_topology_laws hE hD K).2 _).1 hStepOpen 0 hStepZero.
have [d [hd hb]]:=hSem L i e he.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t /andP [ht0 ht].
have hMinL:Num.min r d<=r by rewrite ge_min lexx.
have hMinR:Num.min r d<=d by rewrite ge_min lexx orbT.
have htr:`|t|<r:=lt_le_trans ht hMinL.
have htd:0<`|t|<d by rewrite ht0 /=; exact:(lt_le_trans ht hMinR).
have [g hg]:=subspace_representation_full (smooth_fixed_test_space_laws hE K) (hSupp t htr).
have hEqual:smooth_test_step hE K g=f t.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hg.
rewrite -hEqual; apply:hBall.
change (nu L i (smooth_fixed_test_inclusion hE K (g-0))<e).
by rewrite subr0 hg; exact:hb t htd.
Qed.
End SupportedPuncturedLimit.
