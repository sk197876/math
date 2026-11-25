(** Federer (1969), 4.1.4, p. 349: a fixed original
    unit-mass test identifies the positive-scale scalar limit
    of alpha_e, so the actual small-scale dual constants
    coincide. This is Federer's original argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric ContinuousDualUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  PartialFunctionBasic MeasureVectorIntegralUP EuclideanLebesgueDimensions DistributionIntegralFieldUP
  DistributionConstantDensityAction InnerParallelFamilyUP InnerComponentFamilyUP InnerComponentExhaustion
  CompleteMetricUP NormRegularity SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationIntegral SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily SmoothedDistributionDensityUP
  InnerConstantIntegralEvaluation PositiveNormLimitUP TranslatedKernelExactSupport TranslatedKernelUnitMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularisationConstantScaleIndependence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) DT value).
Variable T:Hom DT R^o.
Variable Q:R->Hom DT DT.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable g:R->X->YD.
Hypothesis hAction:forall e:R,0<e ->
  is_distribution_integral_action (@euclidean_lebesgue_measure R n) ed (g e) value (hom_comp T (Q e)).
Variable A:set X.
Hypothesis hOpen:@open NT A.
Hypothesis hConnected:@connected NT A.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family N A O.
Variable a:X.
Hypothesis ha:A a.
Variable C:R->set X.
Hypothesis hC:@is_inner_component_family R NT O a C.
Hypothesis hConst:forall e:R,0<e ->forall u v,C e u ->C e v ->g e v=g e u.


Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable B:R->X->Hom Y DT.
Hypothesis hBG:@is_smoothed_kernel_density_family R n Y NY hNY E ev hE T YD ed family B g.
Hypothesis hLimit:forall f:DT,
  positive_norm_limit (fun t:R^o=>`|t|) (fun e=>T (Q e f)) (T f).

(** Source for [regularisation_centre_scalar_limit]: the second
    displayed limit in Federer 4.1.4, p. 349. The fixed
    original test Phi_delta(x-a)y proves that the original
    constants have positive-scale limit <y,g_delta(a)>. *)
Theorem regularisation_centre_scalar_limit d (hd:0<d):O d a ->forall y:Y,
  positive_norm_limit (fun t:R^o=>`|t|) (fun e=>ed (g e a) y) (ed (g d a) y).
Proof.
move=>hda y.
have[hB hg]:=@hBG d hd.
pose hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily d hd.
pose hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily d hd.
have hUnit:=@smoothing_dilation_integral_one R n phi family hPhi hFamily d hd.
have hVector:=@translated_kernel_test_unit_integral R n Y NY hNY hY E ev hE
  (family d) hSmooth d hOff hUnit (B d) hB a y.
have hSupp:support (B d a y) `<=` A.
  exact:(@translated_kernel_test_inward_support R n Y NY hNY E ev hE
    (family d) d hOff (B d) hB A O hO hd a hda y).
have hEventual:=@inner_constant_integral_eventual_evaluation R n Y NY hNY E ev hE
  T Q YD ed DN hYD g hAction A hOpen hConnected O hO a ha C hC hConst
  (B d a y) y hSupp hVector.
have hTest:=@hLimit (B d a y).
rewrite -(@hg a y) in hTest.
exact:(@positive_norm_limit_eventual_equality R R^o (fun t:R^o=>`|t|)
  (fun e=>T (Q e (B d a y))) (fun e=>ed (g e a) y) (ed (g d a) y) hEventual hTest).
Qed.

(** Source for [regularisation_centre_scale_independent]:
    alpha_delta is independent of sufficiently small positive
    delta, the final sentence of Federer 4.1.4, p. 349.
    Equality is in the actual continuous dual Y*. *)
Theorem regularisation_centre_scale_independent d e:
  0<d ->0<e ->O d a ->O e a ->g d a=g e a.
Proof.
move=>hd he hda hea.
apply:(continuous_dual_injective hYD); apply:hom_ext=>y.
exact:(@positive_norm_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
  (fun r=>ed (g r a) y) (ed (g d a) y) (ed (g e a) y)
  (@regularisation_centre_scalar_limit d hd hda y)
  (@regularisation_centre_scalar_limit e he hea y)).
Qed.
End RegularisationConstantScaleIndependence.
