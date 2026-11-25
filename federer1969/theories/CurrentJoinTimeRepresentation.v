(** Federer (1969), 4.1.11, pp. 364–365: retain the
    original positive unit-time current, its exact variation
    and its density. These are the segment and time-factor
    laws of 4.1.8–4.1.9, pp. 362–363, on the full time line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  ExteriorGrading ExteriorPowers CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentSegmentMeasureSealed
  OrientedSegmentCurrentSealed OrientedSegmentCurrentRepresentation CurrentUnitRepresentationVariation
  CurrentHomotopyTimeDensity CurrentHomotopyProductOrientation BoundedCurrentDensityUniqueness
  SimpleVectors CurrentJoinDomain DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinTimeRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Time := (fun _:X=>True).
Local Notation N := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hTime := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Local Notation TT := (current_domain R 1%N Time).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_segment_domain R).

(** Source for [current_join_time_vector]: the original
    positive unit-time vector in the first mass display,
    Federer 4.1.11, p. 365, as already used in 4.1.9. *)
Definition current_join_time_vector:exterior_power X 1%N:=
  exterior_first_inclusion X (@euclidean_one_embed R 1-@euclidean_one_embed R 0).

(** Source for [current_join_time_measure]: the original
    interval parameter image, supporting the literal time
    integral in Federer 4.1.11, p. 365. This aliases the
    preceding opaque segment measure. *)
Definition current_join_time_measure:set TT->\bar R:=
  @SegmentCurrentMeasure.value R 1%N Time (@euclidean_one_embed R 0)
    (@euclidean_one_embed R 1) hSegment.

(** Source for [current_join_time_vector_value]: the unit
    time velocity equals the inclusion of the positive
    coordinate vector, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_time_vector_value:current_join_time_vector=
  exterior_first_inclusion X (@euclidean_one_embed R 1).
Proof.
have hZero:@euclidean_one_embed R 0=0 by apply/ffunP=>k;rewrite /euclidean_one_embed !ffunE.
by rewrite /current_join_time_vector hZero subr0.
Qed.

(** Source for [current_join_time_vector_unit]: the
    positive unit-time density has mass one, supporting
    the sharp join integral in Federer 4.1.11, p. 365. *)
Lemma current_join_time_vector_unit:@current_vector_mass R h2 1%N 1%N current_join_time_vector= 1.
Proof. exact:(@current_homotopy_time_velocity_unit R h2). Qed.

(** Source for [current_join_time_vector_simple]: simplicity
    of the time factor alone permits the exact time-product
    variation, supporting Federer 4.1.11, p. 365, by 4.1.8. *)
Lemma current_join_time_vector_simple:simple current_join_time_vector.
Proof. exact:(@current_homotopy_time_simple R). Qed.

(** Source for [current_join_time_representation]: the
    actual time segment has its original Radon velocity
    representation, supporting Federer 4.1.11, pp. 364–365. *)
Theorem current_join_time_representation:
  @is_current_integration_representation R h2 1%N 1%N Time hTime I
    current_join_time_measure (fun _=>current_join_time_vector).
Proof.
exact:(@oriented_segment_current_representation R h2 1%N Time hTime
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) hSegment).
Qed.

(** Source for [current_join_time_representable]: the
    original time factor is representable by integration,
    supporting the mass estimate of Federer 4.1.11, p. 365. *)
Theorem current_join_time_representable:
  @is_integration_representable_current R h2 1%N 1%N Time hTime I.
Proof. exists current_join_time_measure,(fun _=>current_join_time_vector);exact:current_join_time_representation. Qed.

(** Source for [current_join_time_variation]: the actual
    unit interval variation is exactly the original segment
    parameter image, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_time_variation
    (hI:@is_integration_representable_current R h2 1%N 1%N Time hTime I):
  @NormalisedCurrent.measure R h2 1%N 1%N Time hTime I hI=current_join_time_measure.
Proof.
exact:(@current_unit_representation_variation R h2 1%N 1%N Time hTime I
  current_join_time_measure (fun _=>current_join_time_vector) current_join_time_representation
  (fun _=>current_join_time_vector_unit) hI).
Qed.

(** Source for [current_join_time_density_agreement]: the
    original auxiliary time density equals the positive
    unit vector almost everywhere for the original time
    variation, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_time_density_agreement
    (hI:@is_integration_representable_current R h2 1%N 1%N Time hTime I):
  measure_almost_everywhere (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime I hI)
    [set t|@NormalisedCurrent.auxiliary_density R h2 1%N 1%N Time hTime I hI t=current_join_time_vector].
Proof.
have hNormal:=@NormalisedCurrent.laws R h2 1%N 1%N Time hTime I hI.
have hBase:=normalised_distribution_representation_laws hNormal.
have hRep:=current_join_time_representation.
rewrite (current_join_time_variation hI) in hBase *.
have hUnit (t:TT):@current_vector_mass R h2 1%N 1%N current_join_time_vector<=1.
  by rewrite current_join_time_vector_unit.
exact:(@bounded_current_density_almost_unique R h2 1%N 1%N Time hTime
  current_join_time_measure (distribution_representation_measure hRep)
  (distribution_representation_radon hRep)
  (@NormalisedCurrent.auxiliary_density R h2 1%N 1%N Time hTime I hI)
  (fun _=>current_join_time_vector) (distribution_representation_weak_measurable hBase)
  (distribution_representation_weak_measurable hRep)
  (normalised_distribution_density_unit_bound hNormal)
  hUnit
  (@current_value R h2 1%N Time hTime 1%N I)
  (distribution_representation_action hBase) (distribution_representation_action hRep)).
Qed.
End CurrentJoinTimeRepresentation.
