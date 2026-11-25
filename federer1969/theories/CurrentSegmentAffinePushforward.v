(** Federer (1969), 4.1.11, p. 365: the original
    two-point join agrees with the oriented segment of
    4.1.8, p. 362. First identify the affine image of
    the original positive unit interval by its literal
    interval integral, without an injectivity assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorDegreeOneNorm AlternatingForms AlternatingPairing
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMapDifferential CurrentImageDensityPairing CurrentPushforwardSealed CurrentPushforwardIntegralAction
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentSegmentAffineMap CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinTimeRepresentation CurrentJoinTimeIntegral CurrentSegmentMapUP OrientedSegmentCurrentUP
  OrientedSegmentCurrentSealed OrientedSegmentCurrentUnique ConvexMetricSegment
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureIntegralGraphEquivalence MeasureSubsetIntegral LebesgueScalarMeasure SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSegmentAffinePushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Line := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:Line=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:Line) (_:True)=>@norm_full_domain_interior R Line
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TT := (current_domain R 1%N Time).
Variables u v:X.
Local Notation A := (@current_segment_affine_map R n u v).
Local Notation L := (@current_segment_affine_linear R n u v).
Local Notation AImage := (fun (z:Line) (_:Time z)=>Logic.I).
Local Notation AClass := (@current_segment_affine_map_smooth R n u v Time hTime).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation hCompact := (@current_join_time_segment_compact R h2).
Local Notation P := (@current_compact_map_pushforward R h2 1%N n Time Full hTime hFull
  A AImage AClass 1%N Segment hCompact).
Local Notation Proper := (@current_compact_map_proper R h2 1%N n 1%N Time Full hTime
  Segment A AImage (norm_class_continuous (AClass 0%N)) hCompact).
Local Notation mu := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation theta := (@NormalisedCurrent.auxiliary_density R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime Segment hSegment))).
Local Notation velocity := (exterior_first_inclusion X (v-u)).
Local Notation q := (fun t:TT=>@euclidean_one_project R (set_val t)).

(** Source for [current_segment_affine_pushforward_action]:
    the actual affine image of [0,1] has precisely the
    original oriented-segment integral, supporting Federer
    4.1.11, p. 365, by 4.1.8, p. 362. Constant maps
    and zero-dimensional targets are included. *)
Theorem current_segment_affine_pushforward_action:
  @is_oriented_segment_current R h2 n Full hFull u v P.
Proof.
move=>phi.
pose f:=real_total_integrand (fun t=>pairing velocity
  (@current_test_value R h2 n Full hFull 1%N phi (metric_segment_point u v t))).
have hAction:=@current_pushforward_original_integral_action R h2 1%N n 1%N
  Time Full hTime hFull Segment hSegment A AImage AClass Proper phi.
have hScalar:is_measure_integral mu (partial_function_precompose q f)
    (@current_value R h2 n Full hFull 1%N P phi)%:E.
  apply:(@measure_integral_almost_equal R TT mu hm _ _ _ hAction).
  apply:(@measure_almost_everywhere_mono R TT mu hm _ _ _
    (@current_join_time_density_agreement R h2 hSegment))=>t ht.
  have hDensity:@current_image_density R 1%N n 1%N Time A theta t=velocity.
    rewrite /current_image_density
      (@current_segment_affine_map_differential R n u v Time hTime (set_val t) Logic.I).
    change (theta t=@current_join_time_vector R) in ht.
    rewrite ht current_join_time_vector_value exterior_map_first_inclusion.
    change (exterior_first_inclusion X (L (@euclidean_one_embed R 1))=velocity).
    by rewrite current_segment_affine_linear_values euclidean_one_embedK scale1r.
  have hPath:A (set_val t)=metric_segment_point u v (q t).
    rewrite -{1}(euclidean_one_projectK (set_val t)).
    exact:current_segment_affine_map_scalar_values.
  exists (pairing velocity (@current_test_value R h2 n Full hFull 1%N phi (metric_segment_point u v (q t))))%:E.
  split;first by rewrite real_total_integrand_graph hDensity hPath.
  change (partial_function_graph f (q t) (pairing velocity
    (@current_test_value R h2 n Full hFull 1%N phi (metric_segment_point u v (q t))))%:E).
  by rewrite /f real_total_integrand_graph.
exact:(@current_join_time_scalar_integral_iff R h2 hSegment f _).1 hScalar.
Qed.

(** Source for [current_segment_affine_pushforward]: the
    original affine image of the positive unit interval
    equals [u,v], supporting the segment identity in
    Federer 4.1.11, p. 365. The proof uses uniqueness
    of the original all-test interval action. *)
Theorem current_segment_affine_pushforward (hUV:@is_current_segment_domain R n Full u v):
  P=@OrientedSegmentCurrent.value R h2 n Full hFull u v hUV.
Proof.
exact:(@oriented_segment_current_unique R h2 n Full hFull u v P
  (@OrientedSegmentCurrent.value R h2 n Full hFull u v hUV)
  current_segment_affine_pushforward_action (@OrientedSegmentCurrent.laws R h2 n Full hFull u v hUV)).
Qed.
End CurrentSegmentAffinePushforward.
