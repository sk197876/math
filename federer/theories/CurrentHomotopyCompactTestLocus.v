(** Federer (1969), 4.1.9, p. 363: the original
    closed-cylinder properness supplies the compact spatial
    locus needed to interpret the test-action formula for
    arbitrary currents. Source support may be unbounded and
    no integral representation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanBlockNormTopology TopologicalProductMaps CurrentSpaces CurrentCartesianDomain
  SmoothCompactSet CurrentSegmentCompactSet CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentHomotopyCylinder CurrentProperOnContainingSet CurrentHomotopyAvoidCompact ScalarSegmentCoordinateValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyCompactTestLocus.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNT := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation ZT := (real_norm_metric_space hNZ).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Variable T:@current_space R h2 n U hU j.
Local Notation support := (@current_support R h2 n U hU j T).
Local Notation C := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h hGeometry T).
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hGeometry T.
Variable K:smooth_compact_set hNY V.
Local Notation Avoid := (@current_homotopy_avoid_compact R n nu A U V f g h hGeometry K).

(** Source for [current_homotopy_compact_test_locus]: the
    original spatial projection of the compact inverse image
    of a target support under the proper closed cylinder,
    supporting Federer 4.1.9, p. 363. This set is
    specified by the original map and carriers. *)
Definition current_homotopy_compact_test_locus:set X:=
  q @` [set z|C z /\ smooth_compact_carrier K (h z)].

(** Source for [current_homotopy_compact_test_locus_compact]:
    the test locus is compact by the printed properness and
    continuity of the original spatial projection, supporting
    Federer 4.1.9, p. 363. *)
Theorem current_homotopy_compact_test_locus_compact:
  @compact XT current_homotopy_compact_test_locus.
Proof.
have hPre:=@current_containing_proper_compact_preimage R (1+n)%N nu AU V C
  (@current_homotopy_cylinder_in_domain R h2 n nu j A U V f g h hGeometry T) h
  (@current_homotopy_image R n nu A U V f g h hGeometry) hProper K.
have hQ:continuous (fun z:ZT=>(q z:XT)).
  move=>z;exact:(continuous_comp (@euclidean_block_split_norm_continuous R 1%N n z)
    (@second_projection_continuous (real_norm_metric_space hNT) XT (euclidean_block_split z))).
apply:continuous_compact hPre.
exact:continuous_subspaceT hQ.
Qed.

(** Source for [current_homotopy_compact_test_locus_in_domain]:
    the compact projected locus lies in the original source
    domain, supporting the cutoff in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_compact_test_locus_in_domain:
  current_homotopy_compact_test_locus `<=` U.
Proof. move=>x [z [hz hKz] <-];exact:hz.2.1. Qed.

(** Source for [current_homotopy_compact_test_index]: the
    actual compact index for the original source cutoff,
    supporting Federer 4.1.9, p. 363. Only the
    already proved compactness and domain inclusion are packaged. *)
Definition current_homotopy_compact_test_index:smooth_compact_set hNX U:=
  @Build_smooth_compact_set R X NX hNX U current_homotopy_compact_test_locus
    current_homotopy_compact_test_locus_in_domain current_homotopy_compact_test_locus_compact.

(** Source for [current_homotopy_support_compact_or_avoid]:
    every original support point either belongs to the compact
    test locus or its entire time path avoids K, supporting
    the test-action restatement in Federer 4.1.9, p. 363.
    No compactness of the whole current support is inferred. *)
Theorem current_homotopy_support_compact_or_avoid:
  support `<=` (current_homotopy_compact_test_locus `|` Avoid).
Proof.
move=>x hx;case:(pselect (current_homotopy_compact_test_locus x))=>[hP|hP];first by left.
right;split;first exact:hx.1.
move=>a ha hK.
have hFirst:p (euclidean_block_join (a,x))=a:=congr1 fst (@euclidean_block_joinK R 1%N n (a,x)).
have hLast:q (euclidean_block_join (a,x))=x:=congr1 snd (@euclidean_block_joinK R 1%N n (a,x)).
apply:hP;exists (euclidean_block_join (a,x));last exact:hLast.
split;last exact:hK.
split;last by rewrite hLast.
have[t [ht hPoint]]:=@current_segment_compact_points R 1%N AT u v hSegment a ha.
rewrite hFirst hPoint
  scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
by move:ht;rewrite in_itv /=.
Qed.
End CurrentHomotopyCompactTestLocus.
