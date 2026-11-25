(** Federer (1969), 4.1.12, pp. 368–369: the
    oriented intervals in both original examples have
    mass equal to their lengths. Prove the more
    general segment statement from its actual
    probability representation and degree-one mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers CurrentSpaces CurrentDomain
  CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed CurrentSegmentMeasureSealed
  CurrentSegmentMeasureRadon OrientedSegmentCurrentSealed OrientedSegmentCurrentRepresentation
  CurrentExteriorOperatorMassBound CurrentProbabilityDensityMass CurrentMassSealed MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n U u v.
Local Notation S := (@OrientedSegmentCurrent.value R h2 n U hU u v hSegment).
Local Notation gamma := (@SegmentCurrentMeasure.value R n U u v hSegment).
Local Notation velocity := (exterior_first_inclusion X (v-u)).

(** Source for [oriented_segment_current_mass]:
    M([u,v])=|v-u|, the exact interval mass
    used in both series of Federer 4.1.12,
    pp. 368–369, by the literal segment integral
    of 4.1.8, p. 362. Degenerate segments and
    zero-dimensional ambient spaces remain included. *)
Theorem oriented_segment_current_mass:
  @CurrentMass.value R h2 n 1%N U hU S=(NX (v-u))%:E.
Proof.
have hTotal:gamma setT= 1%E.
  rewrite -(@current_segment_measure_image R n U u v hSegment)
    /measure_pushforward preimage_setT.
  exact:current_segment_parameter_total.
apply:(@current_probability_density_mass R h2 n 1%N U hU S gamma (fun _=>velocity)
  (@oriented_segment_current_representation R h2 n U hU u v hSegment) (NX (v-u)) hTotal).
move=>x;exact:(@current_first_vector_mass R h2 n (v-u)).
Qed.
End OrientedSegmentMass.
