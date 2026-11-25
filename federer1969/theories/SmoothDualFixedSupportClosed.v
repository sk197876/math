(** Federer (1969), 4.1.1, p. 344: E' is the
    union of its weakly closed fixed-compact-support
    subsets E'_K. The proof uses support preservation
    under restriction and the actual distribution criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology
  FunctionalSupportUP ContinuousRealDual SmoothDualRestriction SmoothDualCompactImage DistributionFixedSupportClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualFixedSupportClosed.
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
Local Notation EWO := (@continuous_real_dual_weak_opens R E EO hEO).
Local Notation DWO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation rho := (@smooth_dual_test_restriction R X Y NX NY hNX hNY U E ev hE D hD).

(** Source for [smooth_dual_fixed_support_set]: E'_K,
    the original compact-support subset of E',
    Federer 4.1.1, p. 344. *)
Definition smooth_dual_fixed_support_set (K:smooth_compact_set hNX U):set ED:=
  [set T|@smooth_functional_support R X Y NX hNX U E ev (eE T) `<=` smooth_compact_carrier K].

(** Source for [smooth_dual_fixed_support_weakly_closed]:
    E'_K is closed in the original weak E' topology,
    Federer 4.1.1, p. 344. *)
Theorem smooth_dual_fixed_support_weakly_closed (K:smooth_compact_set hNX U):
  EWO (~` smooth_dual_fixed_support_set K).
Proof.
pose DK:=@distribution_fixed_support_set R X Y NX NY hNX hNY U E ev hE D hD K.
have hClosed:=@distribution_fixed_support_weakly_closed R X Y NX NY hNX hNY n b hb U hU E ev hE D hD K.
have hPre:=@smooth_dual_test_restriction_weak_continuous R X Y NX NY hNX hNY U E ev hE D hD
  (~` DK) hClosed.
have hEq:[set T:ED|(~` DK) (rho T)]=~` smooth_dual_fixed_support_set K.
  apply:funext=>T.
  change ((~(@smooth_functional_support R X Y NX hNX U DT (SmoothTestEvaluation.smooth_test_value hE)
    (@continuous_real_dual_evaluation R DT SO hSO (rho T)) `<=` smooth_compact_carrier K))=
    (~(@smooth_functional_support R X Y NX hNX U E ev (eE T) `<=` smooth_compact_carrier K))).
  by rewrite (@smooth_dual_restriction_support R X Y NX NY hNX hNY n b hb U hU E ev hE D hD T).
by rewrite -hEq.
Qed.

(** Source for [smooth_dual_fixed_support_cover]: E' is
    the union of all its closed E'_K subsets,
    Federer 4.1.1, p. 344. *)
Theorem smooth_dual_fixed_support_cover T:
  exists K:smooth_compact_set hNX U,smooth_dual_fixed_support_set K T.
Proof.
exact:(@smooth_dual_support_has_compact_bound R X Y NX NY hNX hNY U hU E ev D hD T).
Qed.
End SmoothDualFixedSupportClosed.
