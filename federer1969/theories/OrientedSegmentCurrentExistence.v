(** Federer (1969), 4.1.8, p. 362: the original
    scalar segment integral defines an actual current on
    every open set containing that segment. The original
    Radon parameter image and constant velocity density
    prove existence without assuming a boundary formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentSegmentParameter CurrentSegmentParameterIntegral CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMeasureSealed CurrentSegmentMeasureRadon CurrentConstantRadonDensity
  OrientedSegmentCurrentUP ConvexMetricSegment OpenCurrentDensityUP OpenCurrentDensitySealed
  DistributionIntegrationRepresentationUP PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  RadonBorelRegularity BorelRegularMeasureUP FiniteRegularPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSegmentCurrentExistence.
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
Local Notation hField := (@current_constant_radon_density_integrable R h2 n 1%N A gamma hGamma hRadon velocity).
Local Notation C := (@OpenCurrentDensity.value R h2 n 1%N A hA gamma hGamma hRadon (fun _=>velocity) hField).
Local Notation ed := (@MultivectorDual.evaluation R X 1%N).

(** Source for [oriented_segment_current_exists]: the
    original printed segment formula defines an actual
    current, Federer 4.1.8, p. 362. Only the original
    containing-domain hypothesis is required, including
    u=v and zero-dimensional ambient space. *)
Theorem oriented_segment_current_exists:
  exists T:@current_space R h2 n A hA 1%N,@is_oriented_segment_current R h2 n A hA u v T.
Proof.
exists C;move=>phi.
pose g (a:AT):=ed velocity (@current_test_value R h2 n A hA 1%N phi (set_val a)).
pose f t:=pairing velocity (@current_test_value R h2 n A hA 1%N phi (metric_segment_point u v t)).
have hRep:=@OpenCurrentDensity.laws R h2 n 1%N A hA gamma hGamma hRadon (fun _=>velocity) hField.
have hAction:=distribution_representation_action hRep phi.
have hTarget:is_measure_integral (measure_pushforward F mu) (real_total_integrand g)
    (@current_value R h2 n A hA 1%N C phi)%:E.
  rewrite (@current_segment_measure_image R n A u v hSegment);exact:hAction.
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm (@current_segment_parameter_radon R)).
have hFinite:(mu setT< +oo)%E.
  rewrite current_segment_parameter_total;change (((1:R)%:E< +oo)%E);exact:ltry.
have hComposed:=(@finite_regular_pushforward_integral_iff R Q AT mu hm hRegular F
  (real_total_integrand g) hFinite _).2 hTarget.
have hActual:is_measure_integral mu (real_total_integrand (fun t:Q=>f (set_val t)))
    (@current_value R h2 n A hA 1%N C phi)%:E.
  apply:(@measure_integral_graph_equivalent R Q mu _ _ _ _ hComposed)=>t z.
  change (partial_function_graph (real_total_integrand g) (F t) z <->
    partial_function_graph (real_total_integrand (fun t:Q=>f (set_val t))) t z).
  by rewrite !real_total_integrand_graph /g /f MultivectorDual.laws
    (@SegmentCurrentPath.laws R n A u v hSegment t).
exact:(@current_segment_parameter_integral_iff R f _).2 hActual.
Qed.
End OrientedSegmentCurrentExistence.
