(** Federer (1969), 4.1.1, p. 345: restriction of a
    continuous smooth functional to tests preserves its support.
    The finite seminorm bound supplies a compact cutoff
    that preserves every original evaluation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  SmoothCutoffReplacement SmoothDualRestriction FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualSupportTransport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Variable L:Hom E R^o.
Hypothesis hL:open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) L.

(** Source for [smooth_dual_annihilation_restriction]: local
    annihilation by a continuous E functional can be tested
    just on D, supporting the common support convention
    for E' and its image in D', Federer 4.1.1, p. 345. *)
Theorem smooth_dual_annihilation_restriction (W:set X):
  @smooth_functional_annihilation_open R X Y NX hNX U E ev L W <->
  @smooth_functional_annihilation_open R X Y NX hNX U DT value (hom_comp L inc) W.
Proof.
split.
- move=>[hW hAnn]; split=>// f hf.
  change (L (inc f)=0); apply:hAnn; exact hf.
- move=>[hW hAnn].
  have [K hAgree]:=@continuous_smooth_functional_cutoff_agreement R X Y NX NY hNX hNY U E ev hE
    D hD n b hb hU L hL.
  split=>// f hf.
  rewrite -(hAgree f).
  change ((hom_comp L inc) (@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f)=0).
  apply:hAnn=>x hx; apply:hf.
  exact:(@smooth_cutoff_replacement_support_subset R X Y NX NY hNX hNY n b hb U hU E ev hE K f x hx).
Qed.

(** Source for [smooth_dual_support_restriction]: the support
    of an E' member equals the support of its restriction
    to D, supporting the compact-support image statement
    in Federer 4.1.1, p. 345. *)
Theorem smooth_dual_support_restriction:
  @smooth_functional_support R X Y NX hNX U E ev L=
  @smooth_functional_support R X Y NX hNX U DT value (hom_comp L inc).
Proof.
apply:funext=>x; apply:propext; split.
- move=>[hx hn]; split=>//.
  move=>[W [hW hxW]]; apply:hn; exists W; split=>//.
  exact:(smooth_dual_annihilation_restriction W).2 hW.
- move=>[hx hn]; split=>//.
  move=>[W [hW hxW]]; apply:hn; exists W; split=>//.
  exact:(smooth_dual_annihilation_restriction W).1 hW.
Qed.
End SmoothDualSupportTransport.
