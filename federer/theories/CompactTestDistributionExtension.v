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
  TestZeroExtensionUP ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactTestDistributionExtension.
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
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Variable K:smooth_compact_set hNX U.
Hypothesis hK:@real_function_support R (real_norm_metric_space hNX) u `<=` smooth_compact_carrier K.
Local Notation P := (@SmoothMultiplier.operator R X Y NX NY hNX hNY U A evA hA u hu).
Local Notation hP := (@SmoothMultiplier.laws R X Y NX NY hNX hNY U A evA hA u hu).
Local Notation M := (@smooth_compact_multiplier_test R X Y NX NY hNX hNY U A evA hA u P hP K hK).
Local Notation rho := (@SmoothRestriction.operator R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A B evA evB hA hB).
Local Notation hRho := (@SmoothRestriction.laws R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A B evA evB hA hB).

(** Source for [compact_test_extension_map]: the original test
    product u times the restriction of a global smooth function,
    supporting T L omega_j in Federer 4.1.2, p. 348. *)
Definition compact_test_extension_map:Hom B TA:=hom_comp M rho.

(** Source for [compact_test_extension_map_value]: exact original
    values of the compact product, Federer 4.1.2, p. 348. *)
Lemma compact_test_extension_map_value g x:U x ->
  smooth_test_value hA (compact_test_extension_map g) x=u x*:evB g x.
Proof.
move=>hx; rewrite /compact_test_extension_map hom_compE /smooth_test_value
  smooth_compact_multiplier_test_evaluation (@hP (rho g) x hx) (@hRho g x hx).
reflexivity.
Qed.

(** Source for [compact_test_extension_map_continuous]: the extension
    product maps E(R^n,Y) continuously into D(U,Y), supporting
    the extension assertion of Federer 4.1.2, p. 348. *)
Theorem compact_test_extension_map_continuous:
  open_family_continuous (smooth_function_opens hDB) SA compact_test_extension_map.
Proof.
have hRC:=@smooth_restriction_continuous R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A B evA evB DA DB hDA hDB rho hRho.
have hMC:=@smooth_compact_multiplier_test_continuous R X Y NX NY hNX hNY U hU
  A evA hA DA hDA u hu P hP K hK.
exact:(@open_family_continuous_compose B A TA (smooth_function_opens hDB)
  (smooth_function_opens hDA) SA rho M hRC hMC).
Qed.

Variable T:Hom TA R^o.
Hypothesis hT:open_family_continuous SA (norm_open_family (@scalar_absolute_value_norm R)) T.

(** Source for [compact_test_distribution_extension_exists]: T L u
    is the restriction of an actual global distribution, Federer 4.1.2,
    p. 348. The chosen extension is first continuous on global E. *)
Theorem compact_test_distribution_extension_exists:
  exists S:DDB,forall f:TB,eB S f=T (compact_test_extension_map (smooth_test_inclusion hB f)).
Proof.
pose L:=hom_comp T (hom_comp compact_test_extension_map (smooth_test_inclusion hB)).
have hInc:=@smooth_test_inclusion_continuous R X Y NX NY hNX hNY (fun _=>True) B evB hB DB hDB.
have hComp:=@open_family_continuous_compose TB B TA SB (smooth_function_opens hDB) SA
  (smooth_test_inclusion hB) compact_test_extension_map hInc compact_test_extension_map_continuous.
have hLC:=@open_family_continuous_compose TB TA R^o SB SA
  (norm_open_family (@scalar_absolute_value_norm R))
  (hom_comp compact_test_extension_map (smooth_test_inclusion hB)) T hComp hT.
have[S hS]:=@continuous_real_dual_represents R TB SB hSB L hLC.
exists S=>f; by rewrite hS /L !hom_compE.
Qed.

(** Source for [compact_test_distribution_extension_original]: the
    global extension restricts exactly to the original product T L u,
    Federer 4.1.2, p. 348. *)
Theorem compact_test_distribution_extension_original
    (L:Hom TA TB) (hL:is_test_zero_extension U (fun _=>True)
      (smooth_test_value hA) (smooth_test_value hB) L)
    (S:DDB) (hS:forall f,eB S f=T (compact_test_extension_map (smooth_test_inclusion hB f))):
  forall f,eB S (L f)=T (@smooth_test_scalar_multiplier R X Y NX NY hNX hNY U A evA hA u hu f).
Proof.
move=>f; rewrite hS; congr (T _).
apply:(smooth_test_values_extensional hA)=>x hx.
rewrite compact_test_extension_map_value // smooth_test_scalar_multiplier_value //.
change (u x*:smooth_test_value hB (L f) x=u x*:smooth_test_value hA f x).
rewrite (@test_zero_extension_original R X Y TA TB U (fun _=>True)
  (smooth_test_value hA) (smooth_test_value hB) L hL f x hx).
reflexivity.
Qed.
End CompactTestDistributionExtension.
