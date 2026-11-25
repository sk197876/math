(** Federer (1969), 4.1.1, pp. 344–345: a continuous
    E functional annihilates any smooth function supported
    away from its support. Compact cutoff replacement and
    the original test partition theorem prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  SmoothCutoffReplacement SmoothDualRestriction SmoothDualSupportTransport
  FunctionalSupportUP SmoothTestFunctionalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualSupport.
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
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U E ev).

(** Source for [smooth_dual_disjoint_support_zero]: T(phi)=0
    for a continuous E functional and any smooth phi
    disjoint from its support, supporting the fixed-support
    identification in Federer 4.1.1, pp. 344–345. *)
Theorem smooth_dual_disjoint_support_zero (L:Hom E R^o) f:
  open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) L ->
  (forall x,tsupport L x ->~support f x) ->L f=0.
Proof.
move=>hL hDisjoint.
have [K hAgree]:=@continuous_smooth_functional_cutoff_agreement R X Y NX NY hNX hNY U E ev hE
  D hD n b hb hU L hL.
pose g:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f.
have hSupport:=@smooth_dual_support_restriction R X Y NX NY hNX hNY n b hb U hU E ev hE D hD L hL.
have hZero:(hom_comp L inc) g=0.
  apply:(@smooth_test_functional_disjoint_support_zero R X Y NX NY hNX hNY n b hb U hU E ev hE
    (hom_comp L inc) g)=>x ht hg.
  rewrite -hSupport in ht.
  apply:(hDisjoint x ht).
  exact:(@smooth_cutoff_replacement_support_subset R X Y NX NY hNX hNY n b hb U hU E ev hE K f x hg).
by rewrite hom_compE (hAgree f) in hZero.
Qed.
End SmoothDualSupport.
