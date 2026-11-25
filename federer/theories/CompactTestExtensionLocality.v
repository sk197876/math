(** Federer (1969), 4.1.4, p. 348: a compact cutoff
    equal to one on a subdomain gives an extension agreeing
    with every original test there and with its derivatives.
    All maps are the actual existing cutoff and zero extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed CompactSupportFunctionUP OpenFamilyTopologyUP NormOpenTopology
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity SmoothRestrictionTestExtension
  SmoothMultiplierUP SmoothMultiplierSealed SmoothCompactMultiplier SmoothTestScalarMultiplier
  TestZeroExtensionUP ContinuousRealDual CompactTestDistributionExtension
  SmoothFunctionSupport TestZeroExtensionLaws TestDirectionalValues TestZeroExtensionDirectional DistributionDirectionalDerivative NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactTestExtensionLocality.
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

Local Notation M := (@compact_test_extension_map R X Y NX NY hNX hNY U hU A B evA evB hA hB u hu K hK).
Local Notation H := (hom_comp M (smooth_test_inclusion hB)).
Local Notation valueA := (smooth_test_value hA).
Local Notation valueB := (smooth_test_value hB).
Local Notation supportA := (@smooth_function_support R X Y NX hNX U TA valueA).
Local Notation supportB := (@smooth_function_support R X Y NX hNX (fun _=>True) TB valueB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U (fun _=>True) valueA valueB L.
Variable W:set X.
Hypothesis hWU:W `<=` U.
Hypothesis hOne:forall x,W x ->u x= 1.

(** Source for [compact_test_extension_local_value]: the compact
    extension product has its original cutoff times the test
    value, used in Federer 4.1.4, p. 348. *)
Lemma compact_test_extension_local_value g x:U x ->valueA (H g) x=u x*:valueB g x.
Proof.
move=>hx; rewrite hom_compE.
exact:(@compact_test_extension_map_value R X Y NX NY hNX hNY U hU A B evA evB hA hB
  u hu K hK (smooth_test_inclusion hB g) x hx).
Qed.

(** Source for [compact_test_extension_local_right_inverse]:
    on tests supported where the cutoff is one, restricting
    by the compact product and extending by zero returns the
    original test, the localization in Federer 4.1.4, p. 348. *)
Theorem compact_test_extension_local_right_inverse g:
  supportB g `<=` W ->L (H g)=g.
Proof.
move=>hSupport.
have hOff x:~W x ->valueB g x=0.
  move=>hx; case:(pselect (valueB g x=0))=>// hNot.
  exact:False_ind _ (hx (hSupport x
    (@smooth_function_nonzero_in_support R X Y NX hNX (fun _=>True) TB valueB g x Logic.I hNot))).
apply:(smooth_test_values_extensional hB)=>x _.
rewrite (@test_zero_extension_value R X Y NX NY hNX hNY U (fun _=>True)
  A B evA evB hA hB L hL (H g) x).
case:(pselect (U x))=>[hxU|hxU].
- rewrite (compact_test_extension_local_value g hxU).
  case:(pselect (W x))=>[hxW|hxW].
  + by rewrite (@hOne x hxW) scale1r.
  + by rewrite (@hOff x hxW) scaler0.
- rewrite (@smooth_test_value_outside R X Y NX NY hNX hNY U A evA hA (H g) x hxU).
  symmetry; apply:hOff=>hxW; exact:hxU (@hWU x hxW).
Qed.

(** Source for [compact_test_extension_local_support]: this
    restriction preserves the exact support of tests in the
    unit plateau, supporting the derivative localization of
    Federer 4.1.4, p. 348. *)
Theorem compact_test_extension_local_support g:
  supportB g `<=` W ->supportA (H g)=supportB g.
Proof.
move=>hSupport.
have h:=@test_zero_extension_support R X Y NX NY hNX hNY U (fun _=>True)
  (fun _ _=>Logic.I) A B evA evB hA hB L hL (H g).
by rewrite (compact_test_extension_local_right_inverse hSupport) in h; symmetry.
Qed.

(** Source for [compact_test_extension_local_left_inverse]:
    a test on U supported in the plateau is recovered after
    zero extension and compact restriction, the agreement
    required in Federer 4.1.4, p. 348. *)
Theorem compact_test_extension_local_left_inverse f:
  supportA f `<=` W ->H (L f)=f.
Proof.
move=>hSupport.
apply:(@test_zero_extension_injective R X Y NX NY hNX hNY U (fun _=>True)
  A B evA evB hA hB L hL).
apply:compact_test_extension_local_right_inverse.
by rewrite (@test_zero_extension_support R X Y NX NY hNX hNY U (fun _=>True)
  (fun _ _=>Logic.I) A B evA evB hA hB L hL f).
Qed.

(** Source for [compact_test_extension_local_directional]: on
    the original unit plateau, compact restriction commutes
    with the actual test derivative. Extension by zero and
    its derivative law prove this without an assumed cutoff
    Leibniz formula, Federer 4.1.4, p. 348. *)
Theorem compact_test_extension_local_directional v g:
  supportB g `<=` W ->
  H (@distribution_test_directional_derivative R X Y NX NY hNX hNY (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior NX x) B evB hB DB hDB v g)=
  @distribution_test_directional_derivative R X Y NX NY hNX hNY U hU A evA hA DA hDA v (H g).
Proof.
move=>hSupport.
apply:(@test_zero_extension_injective R X Y NX NY hNX hNY U (fun _=>True)
  A B evA evB hA hB L hL).
rewrite (@test_zero_extension_directional_commutes R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>Logic.I) A B evA evB hA hB DA DB hDA hDB L hL
  (fun x (_:True)=>norm_full_domain_interior NX x) v (H g)).
rewrite (compact_test_extension_local_right_inverse hSupport).
apply:compact_test_extension_local_right_inverse=>x hx.
apply:hSupport.
exact:(@distribution_test_directional_derivative_support R X Y NX NY hNX hNY (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior NX x) B evB hB DB hDB v g x hx).
Qed.
End CompactTestExtensionLocality.
