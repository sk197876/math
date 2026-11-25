(** Federer (1969), 4.1.12, pp. 368–369:
    the original line-current series share a compact
    scalar interval in R^1. Reuse the actual
    scalar coordinate homeomorphism and original segment
    support law, with the existing Euclidean norm topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology normedtype lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanDistributionMeasureContext
  RealMetricBackground SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentSegmentCompactSet
  OrientedSegmentCurrentSealed OrientedSegmentCurrentSupport ScalarSegmentCoordinateValues ConvexMetricSegment
  NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarCurrentIntervalCompact.
Variable R:realType.
Local Notation X := (R_n R 1%N).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hNX).

(** Source for [scalar_current_embed_continuous]: the
    existing R=R^1 coordinate map is continuous in
    the original current-source topology, supporting
    Federer 4.1.12, pp. 368–369. *)
Lemma scalar_current_embed_continuous:
  continuous (fun t:real_line_metric R=>(euclidean_one_embed t:XT)).
Proof.
move=>t;exact:(continuous_comp (@euclidean_one_embed_continuous R t)
  (@euclidean_distribution_inner_to_norm R 1%N (euclidean_one_embed t))).
Qed.

(** Source for [scalar_current_project_continuous]: the
    inverse original scalar coordinate map is continuous,
    supporting Federer 4.1.12, pp. 368–369. *)
Lemma scalar_current_project_continuous:
  continuous (fun x:XT=>(euclidean_one_project x:real_line_metric R)).
Proof.
move=>x;exact:(continuous_comp (@euclidean_distribution_norm_to_inner R 1%N x)
  (@euclidean_one_project_continuous R x)).
Qed.

(** Source for [scalar_current_closed_interval_compact]: the
    actual coordinate interval a<=x<=b is compact in
    the original source of the two series in
    Federer 4.1.12, pp. 368–369. Empty and
    degenerate intervals are included. *)
Lemma scalar_current_closed_interval_compact (a b:R):
  @compact XT [set x|a<=euclidean_one_project x<=b].
Proof.
have hImage:(fun t:real_line_metric R=>(euclidean_one_embed t:XT)) @` (`[a,b])=
  [set x:XT|a<=euclidean_one_project x<=b].
  apply/seteqP;split.
  - move=>x [t ht <-].
    change (is_true (a<=euclidean_one_project (euclidean_one_embed t)<=b)).
    rewrite euclidean_one_embedK.
    by move:ht;rewrite /mkset in_itv /=.
  - move=>x hx;exists (euclidean_one_project x).
    + by rewrite /mkset in_itv /=.
    + exact:euclidean_one_projectK.
rewrite -hImage.
exact:(continuous_compact (continuous_subspaceT scalar_current_embed_continuous) (@segment_compact R a b)).
Qed.

(** Source for [scalar_current_compact_interval]: the
    literal original coordinate interval used as a
    compact support index, supporting Federer 4.1.12,
    pp. 368–369. It defines no new current. *)
Definition scalar_current_compact_interval (a b:R):smooth_compact_set hNX (fun _:X=>True):=
  @Build_smooth_compact_set R X (inner_norm (@euclidean_inner_productP R 1%N)) hNX
    (fun _=>True) [set x|a<=euclidean_one_project x<=b] (fun _ _=>Logic.I)
    (scalar_current_closed_interval_compact (a:=a) (b:=b)).

(** Source for [scalar_current_compact_interval_carrier]:
    the support index is exactly the stated closed
    scalar interval, supporting Federer 4.1.12,
    pp. 368–369. *)
Lemma scalar_current_compact_interval_carrier a b:
  smooth_compact_carrier (scalar_current_compact_interval a b)=
    [set x|a<=euclidean_one_project x<=b].
Proof. by []. Qed.
End ScalarCurrentIntervalCompact.
Arguments scalar_current_compact_interval (R) a b: clear implicits.
Arguments scalar_current_closed_interval_compact (R) a b: clear implicits.

(** Source for [scalar_current_segment_interval_support]:
    every original oriented scalar subinterval of [a,b]
    has its current support in that same compact
    interval, supporting the original series of Federer
    4.1.12, pp. 368–369. *)
Theorem scalar_current_segment_interval_support (R:realType) (h2:(1+1:R)!=0) (a b c d:R):
  a<=c->c<=d->d<=b->
  @current_support R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N
    (@OrientedSegmentCurrent.value R h2 1%N (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x)
      (euclidean_one_embed c) (euclidean_one_embed d) (@scalar_segment_full_domain R c d)) `<=`
    smooth_compact_carrier (scalar_current_compact_interval R a b).
Proof.
move=>hac hcd hdb x hx.
have hSegment:=@oriented_segment_current_support R h2 1%N (fun _=>True)
  (fun y _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) y)
  (euclidean_one_embed c) (euclidean_one_embed d) (@scalar_segment_full_domain R c d) x hx.
have[t [ht ->]]:=@current_segment_compact_points R 1%N (fun _=>True)
  (euclidean_one_embed c) (euclidean_one_embed d) (@scalar_segment_full_domain R c d) x hSegment.
rewrite scalar_current_compact_interval_carrier /= scalar_segment_parameter_value euclidean_one_embedK.
have hInterval:0<=t<=1 by move:ht;rewrite in_itv /=.
have[ht0 ht1]:=andP hInterval.
have hD:0<=d-c by lra.
have hP0:0<=(d-c)*t:=mulr_ge0 hD ht0.
have hP1:(d-c)*t<=d-c.
  have h:=ler_wpM2l hD ht1;by rewrite mulr1 in h.
apply/andP;split;lra.
Qed.
