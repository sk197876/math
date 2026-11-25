(** Federer (1969), 4.1.12, pp. 368–369: the
    finite oriented-segment sums used in both
    examples are normal. Reuse the actual segment's
    representation, endpoint boundary and compact
    support from 4.1.8–4.1.9. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers CurrentSpaces CurrentDomain
  CurrentSegmentMapUP CurrentSegmentMeasureSealed CurrentSegmentCompactSet OrientedSegmentCurrentSealed
  OrientedSegmentCurrentRepresentation OrientedSegmentCurrentBoundary OrientedSegmentCurrentSupport
  CurrentBoundary CurrentDirac DiracCurrentBounds CurrentIntegrationCriterion CurrentRepresentableLinear
  CurrentSupportGeometry NormalCurrentsUP ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentNormal.
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

(** Source for [oriented_segment_current_normal]:
    the original [u,v] is a normal one-current,
    supporting the two actual series of Federer
    4.1.12, pp. 368–369. Degenerate segments,
    zero-dimensional ambient space and arbitrary
    containing open domains remain included. *)
Theorem oriented_segment_current_normal:
  @is_normal_current R h2 n U hU 1%N S.
Proof.
have h0:(0:R) \in (`[0,1])%R by rewrite in_itv /= lexx ler01.
have h1:(1:R) \in (`[0,1])%R by rewrite in_itv /= ler01 lexx.
have hUu:U u by have h:=@hSegment 0 h0;by rewrite metric_segment_zero in h.
have hUv:U v by have h:=@hSegment 1 h1;by rewrite metric_segment_one in h.
have hDu:=@dirac_current_normal R h2 n U hU u hUu.
have hDv:=@dirac_current_normal R h2 n U hU v hUv.
split.
- split.
  + exists (@SegmentCurrentMeasure.value R n U u v hSegment),
      (fun _=>exterior_first_inclusion X (v-u)).
    exact:(@oriented_segment_current_representation R h2 n U hU u v hSegment).
  + change (@is_integration_representable_current R h2 n 0%N U hU
      (@current_boundary R h2 n 0%N U hU S)).
    rewrite (@oriented_segment_current_boundary R h2 n U hU u v hSegment).
    exact:(@represented_current_difference R h2 n 0%N U hU _ _ hDv.1.1 hDu.1.1).
- exact:(@current_support_compact_bound R h2 n 1%N U hU
    (@current_segment_compact_set R n U u v hSegment) S
    (@oriented_segment_current_support R h2 n U hU u v hSegment)).
Qed.
End OrientedSegmentNormal.
