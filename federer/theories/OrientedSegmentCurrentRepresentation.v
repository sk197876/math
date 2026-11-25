(** Federer (1969), 4.1.9, p. 363: the interval
    factor is representable by integration, as required for
    the displayed deformation-chain orientation. Identify the
    original sealed segment of 4.1.8, p. 362, with its
    original Radon parameter image and constant velocity.
    No second segment current is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentSegmentParameter CurrentSegmentParameterIntegral CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMeasureSealed CurrentSegmentMeasureRadon CurrentConstantRadonDensity
  OrientedSegmentCurrentUP OrientedSegmentCurrentSealed ConvexMetricSegment OpenCurrentDensityUP
  DistributionIntegrationRepresentationUP PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  RadonBorelRegularity BorelRegularMeasureUP FiniteRegularPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSegmentCurrentRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation Q := (current_segment_parameter R).
Local Notation AT := (current_domain R n A).
Local Notation F := (@SegmentCurrentPath.value R n A u v hSegment).
Local Notation mu := (@current_segment_parameter_measure R).
Local Notation hm := (@current_segment_parameter_is_measure R).
Local Notation gamma := (@SegmentCurrentMeasure.value R n A u v hSegment).
Local Notation hGamma := (@current_segment_measure_is_measure R n A u v hSegment).
Local Notation hRadon := (@current_segment_measure_radon R n A hA u v hSegment).
Local Notation velocity := (exterior_first_inclusion X (v-u)).
Local Notation S := (@OrientedSegmentCurrent.value R h2 n A hA u v hSegment).
Local Notation ed := (@MultivectorDual.evaluation R X 1%N).

(** Source for [oriented_segment_current_representation]: the
    actual original segment has its original Radon velocity
    integral representation, supporting the orientation calculation
    in Federer 4.1.9, p. 363, by the literal segment
    formula of 4.1.8, p. 362. Degenerate segments and
    arbitrary original open containing domains are retained. *)
Theorem oriented_segment_current_representation:
  @is_current_integration_representation R h2 n 1%N A hA S gamma (fun _=>velocity).
Proof.
have hField:=@current_constant_radon_density_integrable R h2 n 1%N A gamma hGamma hRadon velocity.
constructor;[exact:hGamma|exact:hRadon|exact:hField.1|exact:hField.2|].
move=>phi.
pose g (a:AT):=ed velocity (@current_test_value R h2 n A hA 1%N phi (set_val a)).
pose f t:=pairing velocity (@current_test_value R h2 n A hA 1%N phi (metric_segment_point u v t)).
change (is_measure_integral gamma (real_total_integrand g)
  (@current_value R h2 n A hA 1%N S phi)%:E).
have hInterval:=@OrientedSegmentCurrent.laws R h2 n A hA u v hSegment phi.
have hActual:=(@current_segment_parameter_integral_iff R f _).1 hInterval.
have hComposed:is_measure_integral mu
    (partial_function_precompose F (real_total_integrand g))
    (@current_value R h2 n A hA 1%N S phi)%:E.
  apply:(@measure_integral_graph_equivalent R Q mu _ _ _ _ hActual)=>t z.
  change (partial_function_graph (real_total_integrand (fun t:Q=>f (set_val t))) t z <->
    partial_function_graph (real_total_integrand g) (F t) z).
  by rewrite !real_total_integrand_graph /g /f MultivectorDual.laws
    (@SegmentCurrentPath.laws R n A u v hSegment t).
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm (@current_segment_parameter_radon R)).
have hFinite:(mu setT< +oo)%E.
  rewrite current_segment_parameter_total;change (((1:R)%:E< +oo)%E);exact:ltry.
have hTarget:=(@finite_regular_pushforward_integral_iff R Q AT mu hm hRegular F
  (real_total_integrand g) hFinite _).1 hComposed.
rewrite (@current_segment_measure_image R n A u v hSegment) in hTarget.
exact:hTarget.
Qed.
End OrientedSegmentCurrentRepresentation.
