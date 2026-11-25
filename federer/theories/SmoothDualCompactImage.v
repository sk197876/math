(** Federer (1969), 4.1.1, pp. 344–345: the
    natural map E' to D' has exactly the distributions
    with compact support as its image. The extension
    witness is proved through the original compact cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology LinearSubspaceRepresentationUP SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothDerivativeSeminormUP
  FunctionalSupportUP SmoothFunctionalSupportBound SmoothDualFiniteBound SmoothDualRestriction
  SmoothDualSupportTransport ContinuousRealDual CompactDistributionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualCompactImage.
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
Local Notation XN := (real_norm_metric_space hNX).
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation ED := (@continuous_real_dual_space R E EO hEO).
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eE := (@continuous_real_dual_evaluation R E EO hEO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation rho := (@smooth_dual_test_restriction R X Y NX NY hNX hNY U E ev hE D hD).
Local Notation sE := (@smooth_functional_support R X Y NX hNX U E ev).
Local Notation sD := (@smooth_functional_support R X Y NX hNX U DT value).

(** Source for [smooth_dual_restriction_support]: the actual
    dual restriction preserves support, supporting the
    compact-support image in Federer 4.1.1, p. 345. *)
Theorem smooth_dual_restriction_support T:sD (eD (rho T))=sE (eE T).
Proof.
have he:eD (rho T)=hom_comp (eE T) inc.
  apply:hom_ext=>f; exact:smooth_dual_test_restriction_evaluation.
rewrite he.
exact:(esym (@smooth_dual_support_restriction R X Y NX NY hNX hNY n b hb U hU E ev hE D hD
  (eE T) (@continuous_real_dual_member_continuous R E EO hEO T))).
Qed.

(** Source for [smooth_dual_support_has_compact_bound]: each
    E' member lies in some E'_K, the union assertion
    in Federer 4.1.1, p. 344. *)
Theorem smooth_dual_support_has_compact_bound T:
  exists K:smooth_compact_set hNX U,sE (eE T) `<=` smooth_compact_carrier K.
Proof.
have [i [K [C [hC hbL]]]]:=(smooth_dual_finite_bound hD (eE T)).1
  (@continuous_real_dual_member_continuous R E EO hEO T).
exists K.
exact:(@smooth_functional_support_within_bound_compact R X Y NX NY hNX hNY U hU E ev D hD
  K i (smooth_function_derivative_seminorm hD K i) (smooth_function_derivative_seminorm_laws hD K i)
  (eE T) C hbL).
Qed.

(** Source for [smooth_dual_support_is_compact]: every E'
    member has compact support, Federer 4.1.1, p. 344,
    by its actual finite derivative-seminorm bound. *)
Theorem smooth_dual_support_is_compact T:compact [set x:XN|sE (eE T) x].
Proof.
have [K hK]:=smooth_dual_support_has_compact_bound T.
exact:(@smooth_functional_support_compact R X Y NX hNX U E ev K (eE T) hK).
Qed.

(** Source for [smooth_dual_restriction_image]: the natural
    E' to D' map has exactly the compactly supported
    distributions in its image, Federer 4.1.1, p. 345. *)
Theorem smooth_dual_restriction_image (S:DD):
  (exists T:ED,rho T=S) <->compact [set x:XN|sD (eD S) x].
Proof.
split.
- move=>[T <-]; rewrite smooth_dual_restriction_support.
  exact:smooth_dual_support_is_compact.
- move=>hCompact.
  pose K:=@Build_smooth_compact_set R X NX hNX U (sD (eD S)) (fun x hx=>hx.1) hCompact.
  have [L [hL [hRestr hSupp]]]:=@compact_distribution_extension_exists R X Y NX NY hNX hNY n b hb
    U hU E ev hE D hD K (eD S) (@continuous_real_dual_member_continuous R DT SO hSO S)
    (fun _ hx=>hx).
  have [T hT]:=@continuous_real_dual_represents R E EO hEO L hL.
  exists T; apply:(subspace_representation_injective (@continuous_real_dual_model_laws R DT SO hSO)).
  apply:hom_ext=>f; rewrite smooth_dual_test_restriction_evaluation hT.
  exact:hRestr.
Qed.
End SmoothDualCompactImage.
