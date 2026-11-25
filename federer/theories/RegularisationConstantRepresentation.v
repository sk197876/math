(** Federer (1969), 4.1.4, pp. 348–349: the global
    distribution is integration against a single continuous
    functional on every test supported in connected A.
    The proof follows the original smoothing and fixed-test
    limits, retaining the actual original scalar integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric ContinuousDualUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  PartialFunctionBasic MeasureVectorIntegralUP EuclideanLebesgueDimensions DistributionIntegralFieldUP
  DistributionConstantDensityAction InnerParallelFamilyUP InnerComponentFamilyUP InnerComponentExhaustion
  CompleteMetricUP NormRegularity SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationIntegral SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily SmoothedDistributionDensityUP
  InnerConstantIntegralEvaluation PositiveNormLimitUP TranslatedKernelExactSupport TranslatedKernelUnitMass
  InnerParallelFamilyLaws RegularisationConstantScaleIndependence GlobalTestVectorIntegral
  ContinuousRealFunctional MeasureIntegralUP SummableRealFunctionUP MeasureIntegralGraphEquivalence WeakDerivativeFieldVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularisationConstantRepresentation.
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


(** Source for [regularisation_constant_vector_representation]:
    the constant alpha represents T on every test supported
    in A, the first displayed conclusion and original proof
    of Federer 4.1.4, pp. 348–349, on the global domain. *)
Theorem regularisation_constant_vector_representation:
  exists c:YD,forall f:DT,forall v:Y,support f `<=` A ->
    is_measure_vector_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun x=>(value f x:real_norm_metric_space hNY))) v ->
    T f=ed c v.
Proof.
have[r [hr hSmall]]:=@inner_parallel_eventually_contains R X N hN A O hO hOpen a ha.
have hd:0<r/2 by lra.
have hdr:r/2<r by lra.
have hCentre:O (r/2) a:=@hSmall (r/2) hd hdr.
exists (g (r/2) a)=>f v hSupp hVector.
have[d [hd0 hEvaluation]]:=@inner_constant_integral_eventual_evaluation R n Y NY hNY E ev hE
  T Q YD ed DN hYD g hAction A hOpen hConnected O hO a ha C hC hConst f v hSupp hVector.
have hEventual:exists d:R,0<d /\ forall e:R,0<e ->e<d ->T (Q e f)=ed (g (r/2) a) v.
  exists (Num.min r d); split; first by rewrite lt_min hr hd0.
  move=>e he hSmallE.
  have /andP [her hed]:(e<r)&&(e<d) by move:hSmallE; rewrite lt_min.
  rewrite (@hEvaluation e he hed).
  have hScale:=@regularisation_centre_scale_independent R n Y NY hNY hY E ev hE
    T Q YD ed DN hYD g hAction A hOpen hConnected O hO a ha C hC hConst
    phi hPhi family hFamily B hBG hLimit e (r/2) he hd (@hSmall e he her) hCentre.
  by rewrite hScale.
have hConstantLimit:=@positive_norm_limit_eventual_equality R R^o (fun t:R^o=>`|t|)
  (fun e=>T (Q e f)) (fun _=>ed (g (r/2) a) v) (T f) hEventual (@hLimit f).
exact:(@positive_norm_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
  (fun _=>ed (g (r/2) a) v) (T f) (ed (g (r/2) a) v) hConstantLimit
  (@positive_norm_limit_constant R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R) _)).
Qed.

(** Source for [regularisation_constant_scalar_integral]: the
    original global-domain conclusion T(f)=integral alpha(f)
    for every test supported in A, Federer 4.1.4, pp. 348–349.
    The functional is actually continuous and every integral
    exists; no conditional integral-value premise remains. *)
Theorem regularisation_constant_scalar_integral:
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` A ->
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (fun x=>alpha (value f x))) (T f)%:E.
Proof.
have[c hRep]:=regularisation_constant_vector_representation.
pose hCont:=@continuous_dual_continuous R Y NY hNY YD ed DN hYD c.
exists (ed c); split; first exact hCont.
move=>f hSupp.
have[v hVector]:=@global_test_vector_integral_exists R n Y NY hNY hY E ev hE f.
have hValue:=@hRep f v hSupp hVector.
rewrite hValue.
have hScalar:=hVector.2 (hom_as_linear (ed c)) hCont.
apply:(measure_integral_graph_equivalent _ hScalar)=>x z.
by rewrite total_functional_evaluation_graph real_total_integrand_graph hom_as_linearE.
Qed.
End RegularisationConstantRepresentation.
