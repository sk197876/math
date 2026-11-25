(** Federer (1969), 4.1.2, p. 348: multiplication by
    a compactly supported scalar on U gives a distribution extending
    to all of R^n. The existing continuous E-to-D multiplier proves
    the extension without a continuity assertion about the final topology's
    joint vector operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed CompactSupportFunctionUP OpenFamilyTopologyUP NormOpenTopology
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity SmoothRestrictionTestExtension
  SmoothMultiplierUP SmoothMultiplierSealed SmoothCompactMultiplier SmoothTestScalarMultiplier
  TestZeroExtensionUP ContinuousRealDual SmoothFunctionSupport CompactTestDistributionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestCutoffExtensionFamily.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY (fun _=>True) evB.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) B evB DB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Local Notation SA := (smooth_test_opens hA hDA).
Local Notation SB := (smooth_test_opens hB hDB).
Local Notation hSA := (smooth_test_final_topology_laws hA hDA).1.
Local Notation hSB := (smooth_test_final_topology_laws hB hDB).1.
Local Notation DDB := (@continuous_real_dual_space R TB SB hSB).
Local Notation eB := (@continuous_real_dual_evaluation R TB SB hSB).

Variable S0:lmodType R.
Variable sv:S0->X->R^o.
Hypothesis hS0:is_smooth_function_space hNX (@scalar_absolute_value_norm R) U sv.
Variable omega:nat->smooth_test_space hS0.
Variable T:Hom TA R^o.
Hypothesis hT:open_family_continuous SA (norm_open_family (@scalar_absolute_value_norm R)) T.

(** Source for [test_cutoff_extension_family_exists]: every T L omega_j
    in Federer 4.1.2, p. 348, has an actual global distribution
    extension. The extension is selected after proving continuity
    of its original compactly supported product action. *)
Theorem test_cutoff_extension_family_exists:
  exists M:nat->Hom B TA,exists A:nat->DDB,
    (forall j,open_family_continuous (smooth_function_opens hDB) SA (M j)) /\
    (forall j g x,U x ->smooth_test_value hA (M j g) x=
      smooth_test_value hS0 (omega j) x*:evB g x) /\
    (forall j f,eB (A j) f=T (M j (smooth_test_inclusion hB f))).
Proof.
have hFor j:exists p:(Hom B TA*DDB)%type,
    open_family_continuous (smooth_function_opens hDB) SA p.1 /\
    (forall g x,U x ->smooth_test_value hA (p.1 g) x=
      smooth_test_value hS0 (omega j) x*:evB g x) /\
    (forall f,eB p.2 f=T (p.1 (smooth_test_inclusion hB f))).
  pose u:=smooth_test_value hS0 (omega j).
  pose hu:=smooth_test_value_smooth hS0 (omega j).
  have[K hK]:=smooth_test_support_bound hS0 (omega j).
  have hReal:@real_function_support R (real_norm_metric_space hNX) u `<=` smooth_compact_carrier K.
    apply:(@real_function_support_in_closed_set R (real_norm_metric_space hNX) u
      (smooth_compact_carrier K)
      (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K))).
    exact:(smooth_function_compact_support_iff hS0 K (smooth_test_inclusion hS0 (omega j))).1 hK.
  pose M:=@compact_test_extension_map R X Y NX NY hNX hNY U hU A B evA evB hA hB
    u hu K hReal.
  have hMC:=@compact_test_extension_map_continuous R X Y NX NY hNX hNY U hU A B evA evB hA hB
    DA DB hDA hDB u hu K hReal.
  have[a ha]:=@compact_test_distribution_extension_exists R X Y NX NY hNX hNY U hU A B evA evB hA hB
    DA DB hDA hDB u hu K hReal T hT.
  exists (M,a); split; first exact hMC.
  split; last exact ha.
  move=>g x hx; exact:(@compact_test_extension_map_value R X Y NX NY hNX hNY U hU
    A B evA evB hA hB u hu K hReal g x hx).
have[F hF]:=choice hFor.
exists (fun j=>(F j).1),(fun j=>(F j).2); split.
- move=>j; exact:(hF j).1.
- split; [move=>j; exact:(hF j).2.1|move=>j; exact:(hF j).2.2].
Qed.
End TestCutoffExtensionFamily.
