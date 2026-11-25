(** Federer (1969), 4.1.1, p. 345: the natural
    map E' to D' embeds every fixed-support subset.
    The exact mapping criterion below characterizes that
    relative embedding without choosing a subtype model
    for the subset of functionals supported in K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology WeakEvaluationTopologyUP WeakEvaluationTopologyLaws
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestTopology SmoothCutoffReplacement FunctionalSupportUP ContinuousRealDual
  SmoothDualRestriction SmoothDualFixedCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FixedSupportWeakEmbedding.
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
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation ED := (@continuous_real_dual_space R E EO hEO).
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eE := (@continuous_real_dual_evaluation R E EO hEO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation EWO := (@continuous_real_dual_weak_opens R E EO hEO).
Local Notation DWO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation rho := (@smooth_dual_test_restriction R X Y NX NY hNX hNY U E ev hE D hD).
Variable K:smooth_compact_set hNX U.

(** Source for [smooth_dual_fixed_support_embedding]: maps
    with values supported in K are E'-weakly continuous
    exactly when their restrictions are D'-weakly continuous.
    Together with injectivity this is the relative embedding
    asserted in Federer 4.1.1, p. 345. *)
Theorem smooth_dual_fixed_support_embedding (A:choiceType) (O:set (set A))
    (hO:is_open_family_topology O) (F:A->ED):
  (forall a,@smooth_functional_support R X Y NX hNX U E ev (eE (F a)) `<=` smooth_compact_carrier K) ->
  (open_family_continuous O EWO F <->
   open_family_continuous O DWO (fun a=>rho (F a))).
Proof.
move=>hSupport; split.
- move=>hF.
  exact:(@open_family_continuous_compose A ED DD O EWO DWO F rho hF
    (@smooth_dual_test_restriction_weak_continuous R X Y NX NY hNX hNY U E ev hE D hD)).
- move=>hRho.
  have hWeakE:=@continuous_real_dual_weak_laws R E EO hEO.
  have hWeakD:=@continuous_real_dual_weak_laws R DT SO hSO.
  apply:(hWeakE.2 A O hO F).2=>f.
  pose g:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f.
  have hEval:(fun a:A=>eE (F a) f)=(fun a=>eD (rho (F a)) g).
    apply:funext=>a; rewrite smooth_dual_test_restriction_evaluation.
    symmetry.
    exact:(@smooth_dual_fixed_cutoff_agreement R X Y NX NY hNX hNY n b hb U hU E ev hE
      D hD K (eE (F a)) (@continuous_real_dual_member_continuous R E EO hEO (F a))
      (hSupport a) f).
  rewrite hEval.
  exact:(@open_family_continuous_compose A DD R^o O DWO
    (norm_open_family (@scalar_absolute_value_norm R)) (fun a=>rho (F a)) (fun T=>eD T g)
    hRho (weak_evaluation_continuous hWeakD g)).
Qed.
End FixedSupportWeakEmbedding.
