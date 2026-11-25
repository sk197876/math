(** Federer (1969), 4.1.8, p. 362: a degenerate
    original segment has zero current. Its actual velocity
    vanishes, and the original scalar interval integral
    has value zero for every actual test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentSpaces CurrentEvaluation CurrentSegmentMapUP OrientedSegmentCurrentUP OrientedSegmentCurrentSealed
  ConvexMetricSegment LebesgueScalarMeasure LatticeL1ApproximationLaws MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSegmentCurrentDegenerate.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variable u:X.
Hypothesis hSegment:@is_current_segment_domain R n A u u.
Local Notation S := (@OrientedSegmentCurrent.value R h2 n A hA u u hSegment).

(** Source for [oriented_segment_current_degenerate]:
    [u,u]=0, the degenerate case of the original
    segment definition, supporting Federer 4.1.8, p. 362. *)
Theorem oriented_segment_current_degenerate:S=0.
Proof.
apply:(@current_values_extensional R h2 n 1%N A hA)=>phi.
have hAction:=@OrientedSegmentCurrent.laws R h2 n A hA u u hSegment phi.
have hPoint:(fun t=>pairing (exterior_first_inclusion X (u-u))
    (@current_test_value R h2 n A hA 1%N phi (metric_segment_point u u t)))=(fun _:R=>0).
  apply:funext=>t;by rewrite subrr /pairing !linear0.
rewrite hPoint in hAction.
have hZero:=@real_total_zero_integral R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R).
have hSubset:=(@real_subset_integral_total R R (@lebesgue_scalar_measure R) `[0,1]
  (fun _=>0) (fun _=>0) (0:R)%:E (fun _ _=>erefl) (fun _ _=>erefl)).2 hZero.
have hValue:=EFin_inj (measure_integral_unique hAction hSubset).
by rewrite hValue linear0 hom_zeroE.
Qed.
End OrientedSegmentCurrentDegenerate.
