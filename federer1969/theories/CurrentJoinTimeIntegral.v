(** Federer (1969), 4.1.11, p. 365: the literal
    time integral and its exact factorial moment.
    Reuse the original time-measure identification from
    4.1.9, pp. 363–364, including partial integrands and infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentSegmentMapUP CurrentSegmentMeasureSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity CurrentHomotopyTimeScalarIntegral
  CurrentConeHomotopyClass CurrentJoinDomain CurrentJoinTimeRepresentation
  ScalarUnitMixedPower ScalarBetaCoefficient ScalarBetaMoment
  RealMetricBackground LebesgueScalarMeasure PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinTimeIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Time := (fun _:X=>True).
Local Notation FullA := (fun _:R=>True).
Local Notation hA := (@current_cone_time_interval R).
Local Notation N := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hTime := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Local Notation TT := (current_domain R 1%N Time).
Local Notation I := (@current_join_time_segment R h2).
Local Notation q := (fun a:TT=>@euclidean_one_project R (set_val a)).
Local Notation oldSegment := (@current_homotopy_time_segment_domain R FullA hA).
Local Notation newSegment := (@current_join_time_segment_domain R).
Local Notation oldRep := (@current_homotopy_time_representable R h2 FullA hA).
Variable hI:@is_integration_representable_current R h2 1%N 1%N Time hTime I.
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime I hI).

(** Source for [current_join_time_scalar_integral_iff]:
    every original partial time integrand has exactly
    its scalar Lebesgue integral on [0,1], supporting the
    mass display in Federer 4.1.11, p. 365. *)
Theorem current_join_time_scalar_integral_iff
    (f:partial_function (real_line_metric R) (extended_real_line R)) b:
  is_measure_integral alpha (partial_function_precompose q f) b<->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1] f b.
Proof.
rewrite (current_join_time_variation hI).
have hOld:=@current_homotopy_time_scalar_integral_iff R h2 FullA hA f b.
rewrite (@current_homotopy_time_variation R h2 FullA hA oldRep) in hOld.
have hProof:oldSegment=newSegment:=Prop_irrelevance _ _.
rewrite hProof in hOld.
exact:hOld.
Qed.

(** Source for [current_join_time_band_conull]: the
    original time variation is concentrated on [0,1],
    supporting the nonnegative time powers in the sharp
    estimate of Federer 4.1.11, p. 365. *)
Theorem current_join_time_band_conull:
  measure_almost_everywhere alpha [set t:TT|0<=q t<=1].
Proof.
rewrite (current_join_time_variation hI).
have hOld:=@current_homotopy_time_band_conull R h2 FullA hA.
rewrite (@current_homotopy_time_variation R h2 FullA hA oldRep) in hOld.
have hProof:oldSegment=newSegment:=Prop_irrelevance _ _.
rewrite hProof in hOld.
exact:hOld.
Qed.

(** Source for [current_join_time_beta_moment]: the
    original time-current variation integrates (1-t)^i t^j
    to exactly i!j!/(i+j+1)!, Federer 4.1.11, p. 365,
    equality of the two mass displays. *)
Theorem current_join_time_beta_moment i j:
  is_measure_integral alpha
    (real_total_integrand (fun t:TT=>@scalar_unit_mixed_power R i j (q t)))
    (@scalar_beta_coefficient R i j)%:E.
Proof.
have hRaw:=(current_join_time_scalar_integral_iff
  (real_total_integrand (@scalar_unit_mixed_power R i j)) _).2 (@scalar_beta_moment R i j).
apply:(@measure_integral_graph_equivalent R TT alpha _ _ _ _ hRaw)=>t v.
by [].
Qed.
End CurrentJoinTimeIntegral.
