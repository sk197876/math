(** Federer (1969), 4.1.13, pp. 369–370: replacing the source
    by an open neighbourhood of the current support preserves the
    original variation integrals. Use the actual test zero extension,
    the original normalized Radon representation of 4.1.7,
    pp. 357–359, and the exact image-integral law of 2.4.18, p. 90.
    Empty domains, degree zero and arbitrary representation witnesses
    are retained. No numerical mass inequality replaces this identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms MultivectorDualSealed CurrentCoefficientNorms CurrentDomain
  CurrentDomainGeometry CurrentSpaces CurrentSupportGeometry
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  CurrentOpenRestriction CurrentAlmostUnitRepresentationVariation
  OpenSubtypeTraceMeasure IsotropyGroupTopology SubtypeCompactHausdorff
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegralFieldUP DistributionVariationDomain SmoothTestEvaluation
  OpenFamilyTopologyMathcomp PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurePushforward
  RadonMeasureUP MeasurableFunctionUP MeasurableGraphEquivalence
  PushforwardMeasurabilityTransfer InjectivePushforwardIntegral
  InjectiveSubsetIntegralTransport MeasureSubsetIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  CovariantMeasureImage ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_open_domain_inclusion]: the unchanged-point
    inclusion of the smaller original source into the larger one in
    Federer 4.1.13, pp. 369–370. This is the preceding public
    topological inclusion, with no chosen inverse or extra point. *)
Definition current_open_domain_inclusion (R:realType) n
    (W U:set (R_n R n)) (hWU:forall x,W x->U x):
    current_domain R n W->current_domain R n U:=
  @open_subtype_inclusion
    (real_norm_metric_space (inner_norm_real_norm
      (@euclidean_inner_productP R n))) W U hWU.

(** Source for [current_open_domain_inclusion_value]: the inclusion
    preserves every original source point, supporting the variation
    integrals in Federer 4.1.13, pp. 369–370. *)
Lemma current_open_domain_inclusion_value (R:realType) n
    (W U:set (R_n R n)) (hWU:forall x,W x->U x)
    (x:current_domain R n W):
  set_val (@current_open_domain_inclusion R n W U hWU x)=set_val x.
Proof. by []. Qed.

Section CurrentOpenRestrictionVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation E := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Variables W U:set X.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hWU:forall x,W x->U x.
Local Notation WT := (current_domain R n W).
Local Notation UT := (current_domain R n U).
Local Notation inc := (@current_open_domain_inclusion R n W U hWU).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` W.
Local Notation S := (@current_open_restriction R h2 n m W U hW hU hWU T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hNormal := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hNormal).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation hr := (distribution_representation_radon hBase).
Local Notation tau := (@open_subtype_trace_measure R XT W U hWU mu).
Local Notation xiW := (fun x:WT=>xi (inc x)).
Local Notation P := (@current_open_test_extension R h2 n m W U hW hU hWU).

(** Source for [current_neighbourhood_variation_trace_measure]: the
    original variation has a measure trace on the smaller source,
    by 2.1.2, p. 54; supporting Federer 4.1.13, pp. 369–370. *)
Lemma current_neighbourhood_variation_trace_measure:is_measure tau.
Proof. exact:(@open_subtype_trace_is_measure R XT W U hWU mu hm). Qed.

(** Source for [current_neighbourhood_variation_trace_radon]: the
    traced original variation is Radon on the smaller original open
    source, by 2.2.5, pp. 62–63; supporting Federer 4.1.13,
    pp. 369–370. The domain may be empty. *)
Lemma current_neighbourhood_variation_trace_radon:is_radon_measure tau.
Proof.
have hOpen:@open XT W.
  rewrite openE=>x hx.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX W x).1 (@hW x hx)).
have hHaus:hausdorff_space WT.
  exact:(@set_type_hausdorff XT W (@metric_hausdorff R XT)).
exact:(@open_subtype_trace_radon R XT W U hWU mu hm hr hOpen
  hHaus (@current_domain_locally_compact R n W hW)).
Qed.

(** Source for [current_neighbourhood_variation_trace_pushforward]:
    inclusion recovers the original variation on every set when the
    smaller source contains the current support. This uses the
    original support-carriage law of 4.1.7, pp. 358–359, in the
    neighbourhood replacement of Federer 4.1.13, pp. 369–370. *)
Lemma current_neighbourhood_variation_trace_pushforward:
  measure_pushforward inc tau=mu.
Proof.
apply:(@open_subtype_carried_trace_pushforward R XT W U hWU mu hm).
apply:(@measure_null_subset R UT mu hm _
  [set x:UT|~@current_support R h2 n U hU m T (set_val x)]).
- move=>x hx hS;exact:hx (@hSupport (set_val x) hS).
- exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
Qed.

(** Source for [current_neighbourhood_restriction_representation]:
    the trace of the original variation and the restriction of its
    actual density represent the restricted current. The original
    test action and all compact norm integrals are transported by
    2.4.18, p. 90; supporting Federer 4.1.13, pp. 369–370. *)
Theorem current_neighbourhood_restriction_representation:
  @is_current_integration_representation R h2 n m W hW S tau xiW.
Proof.
have hTau:=current_neighbourhood_variation_trace_measure.
have hPush:=current_neighbourhood_variation_trace_pushforward.
have hInj:=@open_subtype_inclusion_injective XT W U hWU.
have hCont:=@open_subtype_inclusion_continuous XT W U hWU.
constructor.
- exact:hTau.
- exact:current_neighbourhood_variation_trace_radon.
- have hWeak:=distribution_representation_weak_measurable hBase.
  rewrite -hPush in hWeak.
  have hComp:=measurable_function_pushforward_precompose hInj hWeak.
  exact:(measurable_function_graph_equivalent
    (fun x y=>partial_function_precompose_total inc _ x y) hComp).
- move=>K hK.
  have hImage:compact (inc @` K).
    apply:continuous_compact hK;exact:continuous_subspaceT hCont.
  have hCompactNorm:=distribution_representation_compact_norm hBase.
  have[c hIntegral]:=@hCompactNorm (inc @` K) hImage.
  have hTransport:=(@injective_image_subset_integral_iff R WT UT tau mu
    hTau inc (inc @` K) (real_total_integrand (fun x=>VN (xi x))) c%:E
    hInj hPush).1 hIntegral.
  have hPre:inc @^-1` (inc @` K)=K.
    apply/seteqP;split.
    * move=>x [y hy hyx].
      have hSame:y=x:=hInj y x hyx.
      by rewrite -hSame.
    * move=>x hx;by exists x.
  rewrite hPre in hTransport.
  exists c.
  apply:(measure_integral_graph_equivalent _ hTransport)=>x a.
  rewrite !partial_function_zero_extension_graph.
  by rewrite precompose_total_integrand_graph.
- move=>psi.
  have hIntegral:=distribution_representation_action hBase (P psi).
  change (is_measure_integral mu (real_total_integrand
    (fun x=>@MultivectorDual.evaluation R X m (xi x)
      (@current_test_value R h2 n U hU m (P psi) (set_val x))))
    (@current_value R h2 n U hU m T (P psi))%:E) in hIntegral.
  rewrite -hPush in hIntegral.
  have hTransport:=(@injective_pushforward_integral_iff R WT UT tau hTau inc
    (real_total_integrand (fun x=>@MultivectorDual.evaluation R X m (xi x)
      (@current_test_value R h2 n U hU m (P psi) (set_val x))))
    hInj _).2 hIntegral.
  rewrite current_open_restriction_evaluation.
  apply:(measure_integral_graph_equivalent _ hTransport)=>x a.
  rewrite precompose_total_integrand_graph !real_total_integrand_graph.
  by rewrite /comp current_open_domain_inclusion_value current_open_test_extension_values.
Qed.

(** Source for [current_neighbourhood_restriction_representable]:
    the original restricted current remains representable by
    integration in Federer 4.1.13, pp. 369–370. This is proved from
    its unchanged test action, not assumed as a measure premise. *)
Theorem current_neighbourhood_restriction_representable:
  @is_integration_representable_current R h2 n m W hW S.
Proof.
exists tau,xiW;exact:current_neighbourhood_restriction_representation.
Qed.

(** Source for [current_neighbourhood_variation_trace]: the actual
    original variation of the restricted current equals the trace of
    the original variation, by the almost-unit density identity of
    4.1.7, pp. 357–358; supporting Federer 4.1.13, pp. 369–370.
    Every original representability witness for the restriction is allowed. *)
Theorem current_neighbourhood_variation_trace
    (hSmall:@is_integration_representable_current R h2 n m W hW S):
  @NormalisedCurrent.measure R h2 n m W hW S hSmall=tau.
Proof.
have hPush:=current_neighbourhood_variation_trace_pushforward.
have hUnit:measure_almost_everywhere tau [set x:WT|VN (xiW x)= 1].
  have h:=normalised_distribution_density_unit_norm hNormal.
  rewrite -hPush in h.
  exact:h.
exact:(@current_almost_unit_representation_variation R h2 n m W hW
  S tau xiW current_neighbourhood_restriction_representation hUnit hSmall).
Qed.

(** Source for [current_neighbourhood_variation_pushforward]:
    inclusion carries the restricted current's original variation
    exactly to the original variation on every set, by 4.1.7,
    pp. 357–359; supporting Federer 4.1.13, pp. 369–370.
    This is an equality, with arbitrary original representation witnesses. *)
Theorem current_neighbourhood_variation_pushforward
    (hSmall:@is_integration_representable_current R h2 n m W hW S):
  measure_pushforward inc
    (@NormalisedCurrent.measure R h2 n m W hW S hSmall)=mu.
Proof.
rewrite (current_neighbourhood_variation_trace hSmall).
exact:current_neighbourhood_variation_trace_pushforward.
Qed.

(** Source for [current_neighbourhood_variation_integral_iff]: the
    actual variation integrals before and after the source replacement
    agree with their original partial domains, by 2.4.18, p. 90;
    supporting Federer 4.1.13, pp. 369–370. Every defined signed or
    infinite value is retained, without an integrability hypothesis. *)
Theorem current_neighbourhood_variation_integral_iff
    (hSmall:@is_integration_representable_current R h2 n m W hW S)
    (f:partial_function UT (extended_real_line R)) a:
  is_measure_integral (@NormalisedCurrent.measure R h2 n m W hW S hSmall)
    (partial_function_precompose inc f) a<->is_measure_integral mu f a.
Proof.
have hSmallMeasure:=distribution_representation_measure
  (normalised_distribution_representation_laws
    (@NormalisedCurrent.laws R h2 n m W hW S hSmall)).
have hInj:=@open_subtype_inclusion_injective XT W U hWU.
have h:=@injective_pushforward_integral_iff R WT UT
  (@NormalisedCurrent.measure R h2 n m W hW S hSmall)
  hSmallMeasure inc f hInj a.
by rewrite (current_neighbourhood_variation_pushforward hSmall) in h.
Qed.

(** Source for [current_neighbourhood_variation_total_integral_iff]:
    the printed real weights in the original variation integrals of
    Federer 4.1.13, pp. 369–370, retain their exact values under
    source inclusion. This is the total real instance of 2.4.18,
    p. 90. No positivity, finite integral or nonempty-source premise
    is needed for this equivalence. *)
Theorem current_neighbourhood_variation_total_integral_iff
    (hSmall:@is_integration_representable_current R h2 n m W hW S)
    (F:UT->R) a:
  is_measure_integral (@NormalisedCurrent.measure R h2 n m W hW S hSmall)
    (real_total_integrand (fun x=>F (inc x))) a<->
  is_measure_integral mu (real_total_integrand F) a.
Proof.
have h:=current_neighbourhood_variation_integral_iff hSmall
  (real_total_integrand F) a.
have hGraph:forall x y,
    partial_function_graph
      (partial_function_precompose inc (real_total_integrand F)) x y<->
    partial_function_graph (real_total_integrand (fun x=>F (inc x))) x y.
  move=>x y;exact:precompose_total_integrand_graph.
split=>hIntegral.
- apply:h.1.
  exact:(measure_integral_graph_equivalent
    (fun x y=>iff_sym (hGraph x y)) hIntegral).
- exact:(measure_integral_graph_equivalent hGraph (h.2 hIntegral)).
Qed.
End CurrentOpenRestrictionVariation.
