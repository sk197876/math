(** Federer (1969), 4.1.14, p. 371: changing
    the open time neighbourhood leaves the original
    interval current unchanged after inclusion. The
    all-test interval action of 4.1.8, p. 362,
    and exact zero extension prove this directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorPowers AlternatingPairing CurrentSpaces CurrentOpenRestriction
  CurrentSegmentMapUP CurrentSegmentCompactSet ConvexMetricSegment
  OrientedSegmentCurrentUP OrientedSegmentCurrentSealed OrientedSegmentCurrentUnique
  OrientedSegmentCurrentSupport CurrentCompactMapProper CurrentOpenIdentitySmooth
  CurrentCompactPushforwardAlgebra CurrentNeighbourhoodInclusion
  CurrentPushforwardSealed MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentOpenRestriction.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U W : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hW : forall x, W x -> norm_domain_interior NX W x.
Hypothesis hWU : forall x, W x -> U x.
Variables u v : X.
Hypothesis hSegmentU : @is_current_segment_domain R n U u v.
Hypothesis hSegmentW : @is_current_segment_domain R n W u v.
Local Notation Large := (@OrientedSegmentCurrent.value R h2 n U hU u v hSegmentU).
Local Notation Small := (@OrientedSegmentCurrent.value R h2 n W hW u v hSegmentW).
Local Notation Restrict := (@current_open_restriction R h2 n 1%N W U hW hU hWU).

(** Source for [oriented_segment_open_restriction]: the original
    segment action is preserved by restriction to any open
    set containing the segment, supporting the time-domain
    independence of Federer 4.1.14, p. 371. Degenerate
    segments and empty containing domains remain allowed. *)
Theorem oriented_segment_open_restriction : Restrict Large=Small.
Proof.
apply: (@oriented_segment_current_unique R h2 n W hW u v (Restrict Large) Small
  _ (@OrientedSegmentCurrent.laws R h2 n W hW u v hSegmentW)).
move=> phi.
pose extended := @current_open_test_extension R h2 n 1%N W U hW hU hWU phi.
have hLaw := @OrientedSegmentCurrent.laws R h2 n U hU u v hSegmentU extended.
have hValues :
    (fun t:R => pairing (exterior_first_inclusion X (v-u))
      (@current_test_value R h2 n U hU 1%N extended (metric_segment_point u v t)))=
    (fun t:R => pairing (exterior_first_inclusion X (v-u))
      (@current_test_value R h2 n W hW 1%N phi (metric_segment_point u v t))).
  apply: funext=> t.
  by rewrite /extended current_open_test_extension_values.
rewrite hValues in hLaw.
rewrite current_open_restriction_evaluation.
exact: hLaw.
Qed.

(** Source for [oriented_segment_open_inclusion]: identity
    inclusion recovers the original segment on the larger
    open domain, supporting Federer 4.1.14, p. 371.
    Every actual compactness witness is accepted; no later
    theorem about equality only on support is used. *)
Theorem oriented_segment_open_inclusion
    (hCompact : @compact (real_norm_metric_space hNX)
      (@current_support R h2 n W hW 1%N Small)) :
  @current_compact_map_pushforward R h2 n n W U hW hU (fun x:X => x)
    hWU (@current_open_identity_smooth R n W hW) 1%N Small hCompact=Large.
Proof.
have hRestriction := oriented_segment_open_restriction.
have hSupport : @current_support R h2 n U hU 1%N Large `<=` W.
  move=> x hx.
  have hK := @oriented_segment_current_support R h2 n U hU u v hSegmentU x hx.
  have [t [ht ->]] := @current_segment_compact_points R n U u v hSegmentU x hK.
  exact: @hSegmentW t ht.
have hRCompact : @compact (real_norm_metric_space hNX)
    (@current_support R h2 n W hW 1%N (Restrict Large)).
  by rewrite hRestriction.
pose hId := @current_open_identity_smooth R n W hW.
pose hProper := @current_compact_map_proper R h2 n n 1%N W U hW
  (Restrict Large) (fun x:X => x) hWU
  (norm_class_continuous (hId 0%N)) hRCompact.
have hRecovery := @current_neighbourhood_inclusion_recovery R h2 n 1%N W U
  hW hU hWU hId Large hSupport hProper.
have hSame := @current_compact_map_pushforward_congruence R h2 n n W U hW hU
  (fun x:X => x) hWU hId 1%N (Restrict Large) Small hRCompact hCompact hRestriction.
exact: eq_trans (esym hSame) hRecovery.
Qed.
End OrientedSegmentOpenRestriction.
