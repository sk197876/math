(** Federer (1969), 4.1.9, p. 363: the original unit
    time interval has the scalar parameter image as its
    exact variation measure and the positive unit time vector
    as its original orienting field almost everywhere. Reuse
    the checked original segment and the top-coordinate mass
    normalization of 4.1.7, p. 358. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate ExteriorGrading ExteriorPowers
  FiniteExteriorPowers CurrentDomain CurrentSpaces CurrentCoefficientNorms EuclideanTopCurrentMass
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentOriginalDensityAgreement
  CurrentUnitRepresentationVariation CurrentSegmentMeasureSealed OrientedSegmentCurrentRepresentation
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment ScalarSegmentCoordinateValues
  PartialFunctionUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyTimeDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hA).
Local Notation S := (@current_homotopy_time_segment R A hA h2).
Local Notation Q := (current_domain R 1%N AT).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N) (v-u)).
Local Notation gamma := (@SegmentCurrentMeasure.value R 1%N AT u v hSegment).

(** Source for [current_homotopy_time_velocity_unit]: the
    original positive time velocity has mass one, supporting
    the product orientation in Federer 4.1.9, p. 363.
    The original time interval A need not be bounded. *)
Theorem current_homotopy_time_velocity_unit:
  @current_vector_mass R h2 1%N 1%N velocity= 1.
Proof.
rewrite scalar_segment_velocity subr0 scale1r.
exact:(@euclidean_top_current_vector_mass_one R h2 1%N).
Qed.

(** Source for [current_homotopy_time_representable]: the
    actual original time factor has a Radon integral
    representation, supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_time_representable:
  @is_integration_representable_current R h2 1%N 1%N AT hAT S.
Proof.
exists gamma,(fun _:Q=>velocity).
exact:(@oriented_segment_current_representation R h2 1%N AT hAT u v hSegment).
Qed.

(** Source for [current_homotopy_time_variation]: the exact
    original variation is the original scalar parameter image
    on every set in the original open time domain, supporting
    Federer 4.1.9, p. 363. *)
Theorem current_homotopy_time_variation
    (hS:@is_integration_representable_current R h2 1%N 1%N AT hAT S):
  @NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS=gamma.
Proof.
exact:(@current_unit_representation_variation R h2 1%N 1%N AT hAT S gamma (fun _:Q=>velocity)
  (@oriented_segment_current_representation R h2 1%N AT hAT u v hSegment)
  (fun _=>current_homotopy_time_velocity_unit) hS).
Qed.

(** Source for [current_homotopy_time_original_orientation]:
    the original partial time orientation equals the positive
    unit velocity almost everywhere for the original interval
    measure, supporting the displayed orientation formula in
    Federer 4.1.9, p. 363. Its partial domain is retained. *)
Theorem current_homotopy_time_original_orientation
    (hS:@is_integration_representable_current R h2 1%N 1%N AT hAT S):
  measure_almost_everywhere gamma [set t:Q|
    partial_function_graph (@CurrentOrientation.value R h2 1%N 1%N AT hAT S hS) t velocity].
Proof.
apply:(@current_original_unit_density_agreement R h2 1%N 1%N AT hAT S hS gamma (fun _:Q=>velocity)
  (@oriented_segment_current_representation R h2 1%N AT hAT u v hSegment)).
- move=>t;by rewrite current_homotopy_time_velocity_unit.
- exact:current_homotopy_time_variation.
Qed.
End CurrentHomotopyTimeDensity.
