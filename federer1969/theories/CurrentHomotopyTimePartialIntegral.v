(** Federer (1969), 4.1.9, pp. 363–364: the
    exact scalar time integral for the original unit
    segment. Its variation has the scalar restricted
    Lebesgue measure under the original R^1 coordinate.
    Partial domains and infinite integral values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology normedtype ring.
From Federer Require Import ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMeasureSealed CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  ScalarSegmentCoordinateValues PartialFunctionUP PartialFunctionPrecomposition PartialFunctionSourceImage
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasurePushforward MeasureRestriction OpenSubspaceMeasure LebesgueScalarMeasure RealMetricBackground
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  InjectivePushforwardIntegral RestrictedIntegralIdentity MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTimePartialIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable A:set R.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation TT := (current_domain R 1%N AT).
Local Notation q := (fun a:TT=>@euclidean_one_project R (set_val a)).

(** Source for [current_homotopy_time_project_injective]: the
    original R^1-to-R coordinate is injective on the
    original relative time domain, supporting the integral
    transport in Federer 4.1.9, pp. 363–364. *)
Lemma current_homotopy_time_project_injective:injective q.
Proof.
move=>a b hEqual.
have hVectors:set_val a=set_val b:=can_inj (@euclidean_one_projectK R) hEqual.
exact:val_inj hVectors.
Qed.

(** Source for [current_homotopy_scalar_time_integrand]: the
    original partial time integrand in scalar coordinates,
    supporting Federer 4.1.9, pp. 363–364. Its
    domain is the exact coordinate image of its original
    domain; values outside A are not supplied. *)
Definition current_homotopy_scalar_time_integrand (f:partial_function TT (extended_real_line R)):
    partial_function (real_line_metric R) (extended_real_line R):=
  @partial_function_source_image TT (real_line_metric R) (extended_real_line R)
    q current_homotopy_time_project_injective f.

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

(** Source for [current_homotopy_time_scalar_image]: the
    exact original time variation becomes Lebesgue measure
    restricted to [0,1] in scalar coordinates, supporting
    Federer 4.1.9, pp. 363–364. This is an all-set
    image identity on the original carriers. *)
Theorem current_homotopy_time_scalar_image:
  measure_pushforward q alpha=measure_restrict Leb I.
Proof.
have hPath t:q (Path t)=set_val t.
  change (@euclidean_one_project R (set_val (Path t))=set_val t).
  rewrite (@SegmentCurrentPath.laws R 1%N AT u v hSegment t)
    scalar_segment_parameter_value euclidean_one_embedK.
  ring.
have hImage:measure_pushforward q alpha=measure_pushforward (fun t:Q=>(set_val t:real_line_metric R)) parameterMeasure.
  apply:funext=>B.
  change (alpha (q @^-1` B)=parameterMeasure ((fun t:Q=>(set_val t:real_line_metric R)) @^-1` B)).
  rewrite (@current_homotopy_time_variation R h2 A hA hS)
    ((@SegmentCurrentMeasure.laws R 1%N AT u v hSegment).2 (q @^-1` B)).
  congr (parameterMeasure _);apply:funext=>t.
  change (B (q (Path t))=B (set_val t));exact:(congr1 B (@hPath t)).
rewrite hImage.
exact:(@open_subspace_measure_pushforward R (real_line_metric R) I Leb).
Qed.

(** Source for [current_homotopy_time_partial_integral_iff]:
    integration against the original segment variation is
    exactly the literal scalar subset integral over [0,1],
    supporting Federer 4.1.9, pp. 363–364. Every
    original partial extended-real integrand is included. *)
Theorem current_homotopy_time_partial_integral_iff
    (f:partial_function TT (extended_real_line R)) a:
  is_measure_integral alpha f a <->
  is_measure_subset_integral Leb I (current_homotopy_scalar_time_integrand f) a.
Proof.
have hTransport:=@injective_pushforward_integral_iff R TT (real_line_metric R)
  alpha hAlpha q (current_homotopy_scalar_time_integrand f) current_homotopy_time_project_injective a.
rewrite current_homotopy_time_scalar_image in hTransport.
have hI:measure_measurable Leb I.
  apply:(borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:closed_borel_set (@segment_closed_real R 0 1).
have hSource:is_measure_integral alpha f a <->
    is_measure_integral alpha (partial_function_precompose q (current_homotopy_scalar_time_integrand f)) a.
  split=>hIntegral;apply:(@measure_integral_graph_equivalent R TT alpha _ _ a _ hIntegral)=>t z.
  - exact:iff_sym (@partial_function_source_image_cancel TT (real_line_metric R) (extended_real_line R)
      q current_homotopy_time_project_injective f t z).
  - exact:(@partial_function_source_image_cancel TT (real_line_metric R) (extended_real_line R)
      q current_homotopy_time_project_injective f t z).
exact:(iff_trans hSource (iff_trans hTransport
  (@restricted_integral_zero_extension_iff R (real_line_metric R) Leb
    (@lebesgue_scalar_is_measure R) I (current_homotopy_scalar_time_integrand f) a hI))).
Qed.
End CurrentHomotopyTimePartialIntegral.
