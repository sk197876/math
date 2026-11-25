(** Federer (1969), 4.1.9, p. 363: compact source
    support makes the original closed time cylinder compact
    and its actual homotopy restriction proper. Reuse the
    original segment compact image, Cartesian compactness and
    compact-source properness. The time interval A may be unbounded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain CurrentCartesianCompact CurrentProperOnContainingSet
  CurrentCompactContainingProper CurrentSegmentCompactSet CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyCylinder ScalarSegmentCoordinateValues
  SmoothCompactSet ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyCompactCylinder.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Variable T:@current_space R h2 n U hU j.
Hypothesis hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n U hU j T).
Local Notation support := (@current_support R h2 n U hU j T).
Local Notation C := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h geometry T).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation AU := (@current_homotopy_product_domain R n A U).

(** Source for [current_homotopy_compact_cylinder]: the exact
    original {t:0<=t<=1} times spt T is compact when
    T has compact support, supporting the point-current
    argument in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_compact_cylinder:@compact (real_norm_metric_space hNZ) C.
Proof.
have hBand a:smooth_compact_carrier KTime a<->0<=@euclidean_one_project R a<=1.
  split.
  - move=>ha;have[t [ht ->]]:=@current_segment_compact_points R 1%N AT u v hSegment a ha.
    rewrite scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
    by move:ht;rewrite in_itv /=.
  - move=>ha.
    have hTime:(@euclidean_one_project R a) \in (`[0,1])%R by rewrite in_itv /=.
    have hPoint:=@current_segment_point_in_compact R 1%N AT u v hSegment (@euclidean_one_project R a) hTime.
    by rewrite scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_projectK in hPoint.
have hEqual:C=@euclidean_cartesian_set R 1%N n (smooth_compact_carrier KTime) support.
  apply:funext=>z;apply:propext.
  change ((0<=@euclidean_one_project R (@euclidean_first_block_map R 1%N n z)<=1 /\
    support (@euclidean_last_block_map R 1%N n z))<->
    (smooth_compact_carrier KTime (@euclidean_first_block_map R 1%N n z) /\
      support (@euclidean_last_block_map R 1%N n z))).
  split;move=>[ht hx];split=>//;exact:(hBand _).2 ht || exact:(hBand _).1 ht.
rewrite hEqual.
exact:(@current_cartesian_compact R 1%N n (smooth_compact_carrier KTime) support
  (smooth_compact_is_compact KTime) hCompact).
Qed.

(** Source for [current_homotopy_compact_support_proper]: the
    printed homotopy properness hypothesis holds automatically
    for compactly supported T, supporting the point-current
    proof in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_compact_support_proper:
  @is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Proof.
exact:(@current_compact_containing_map_proper R (1+n)%N nu AU V C
  (@current_homotopy_cylinder_in_domain R h2 n nu j A U V f g h geometry T) h
  (@current_homotopy_image R n nu A U V f g h geometry)
  (norm_class_continuous (hHomotopy.2 0%N)) current_homotopy_compact_cylinder).
Qed.
End CurrentHomotopyCompactCylinder.
