(** Federer (1969), 4.1.9, pp. 363–364: the
    exact scalar time integral for the original unit
    segment. Its variation has the scalar restricted
    Lebesgue measure under the original R^1 coordinate.
    Partial domains and infinite integral values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMeasureSealed CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  ScalarSegmentCoordinateValues PartialFunctionUP PartialFunctionPrecomposition PartialFunctionSourceImage
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasurePushforward MeasureRestriction OpenSubspaceMeasure LebesgueScalarMeasure RealMetricBackground
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  CurrentHomotopyTimePartialIntegral MeasureBasic MeasureAlmostUP
  InjectivePushforwardIntegral RestrictedIntegralIdentity MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTimeScalarIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable A:set R.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation TT := (current_domain R 1%N AT).
Local Notation q := (fun a:TT=>@euclidean_one_project R (set_val a)).

Hypothesis hA:@is_homotopy_parameter_interval R A.
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation S := (@current_homotopy_time_segment R A hA h2).
Local Notation hS := (@current_homotopy_time_representable R h2 A hA).
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS).
Local Notation hAlpha := (distribution_representation_measure
  (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 1%N 1%N AT hAT S hS))).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hA).
Local Notation Q := (current_segment_parameter R).
Local Notation parameterMeasure := (@current_segment_parameter_measure R).
Local Notation Path := (@SegmentCurrentPath.value R 1%N AT u v hSegment).
Local Notation Leb := (@lebesgue_scalar_measure R).
Local Notation I := (`[0,1]:set (real_line_metric R)).


(** Source for [current_homotopy_time_scalar_integral_iff]:
    a scalar integrand in the original time coordinate
    has exactly its literal [0,1] integral, supporting
    the affine estimates in Federer 4.1.9, p. 364.
    Every partial extended-real integrand is retained. *)
Theorem current_homotopy_time_scalar_integral_iff
    (f:partial_function (real_line_metric R) (extended_real_line R)) b:
  is_measure_integral alpha (partial_function_precompose q f) b<->
  is_measure_subset_integral Leb I f b.
Proof.
have hTransport:=@injective_pushforward_integral_iff R TT (real_line_metric R)
  alpha hAlpha q f (@current_homotopy_time_project_injective R A) b.
rewrite (@current_homotopy_time_scalar_image R h2 A hA) in hTransport.
have hI:measure_measurable Leb I.
  apply:(borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:closed_borel_set (@segment_closed_real R 0 1).
exact:(iff_trans hTransport (@restricted_integral_zero_extension_iff R (real_line_metric R)
  Leb (@lebesgue_scalar_is_measure R) I f b hI)).
Qed.

(** Source for [current_homotopy_time_band_conull]: the
    actual interval-current variation is concentrated on
    the original closed time band, supporting the affine
    mass integrals in Federer 4.1.9, p. 364.
    No assertion is made at times outside that band. *)
Theorem current_homotopy_time_band_conull:
  measure_almost_everywhere alpha [set a:TT|0<=q a<=1].
Proof.
change (alpha (q @^-1` (~` I))=0%E).
change (measure_pushforward q alpha (~` I)=0%E).
rewrite (@current_homotopy_time_scalar_image R h2 A hA) /measure_restrict setICr.
exact:measure_empty (@lebesgue_scalar_is_measure R).
Qed.
End CurrentHomotopyTimeScalarIntegral.
