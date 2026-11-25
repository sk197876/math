(** Federer (1969), 4.1.9, p. 363: the actual
    oriented segment is supported in its original
    closed segment. Its printed integral in 4.1.8,
    p. 362, and the preceding support criterion
    give this without an additional representation hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentSpaces CurrentSupportGeometry SmoothCompactSet SmoothFunctionSupport CurrentSegmentMapUP
  CurrentSegmentCompactSet OrientedSegmentCurrentUP OrientedSegmentCurrentSealed ConvexMetricSegment
  LebesgueScalarMeasure LatticeL1ApproximationLaws MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralUniqueness RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentCurrentSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior NX A x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation S := (@OrientedSegmentCurrent.value R h2 n A hA u v hSegment).
Local Notation DT := (@current_test_space R h2 n A hA 1%N).
Local Notation value := (@current_test_value R h2 n A hA 1%N).
Local Notation K := (@current_segment_compact_set R n A u v hSegment).

(** Source for [oriented_segment_current_support]: the
    original current [u,v] is supported in its
    exact closed segment, supporting the precise
    cylinder properness in Federer 4.1.9, p. 363,
    by the original formula of 4.1.8, p. 362. *)
Theorem oriented_segment_current_support:
  @current_support R h2 n A hA 1%N S `<=` smooth_compact_carrier K.
Proof.
apply:(@current_support_compact_criterion R h2 n 1%N A hA K S).2=>phi hPhi.
pose integrand t:=pairing (exterior_first_inclusion X (v-u))
  (value phi (metric_segment_point u v t)).
have hZero t (ht:t \in (`[0,1])%R):integrand t=0.
  have hPoint:=@current_segment_point_in_compact R n A u v hSegment t ht.
  have hValue:value phi (metric_segment_point u v t)=0.
    apply:contrapT=>hNo.
    have hSupport:=@smooth_function_nonzero_in_support R X (A_m X R^o 1%N) NX hNX A DT
      value phi (metric_segment_point u v t) (@hSegment t ht) hNo.
    exact:(hPhi _ hSupport).2 hPoint.
  by rewrite /integrand hValue (bil0r (@pairing_bilinear R X R^o 1%N)).
have hIntegral:=@real_total_zero_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R).
have hSubset:=(@real_subset_integral_total R R (@lebesgue_scalar_measure R) (`[0,1]:set R)
  integrand (fun _=>0) (0:R)%:E (fun t ht=>esym (hZero t ht)) (fun _ _=>erefl)).2 hIntegral.
exact:(EFin_inj (measure_integral_unique
  (@OrientedSegmentCurrent.laws R h2 n A hA u v hSegment phi) hSubset)).
Qed.
End OrientedSegmentCurrentSupport.
