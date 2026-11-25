(** Federer (1969), 4.1.9, p. 363: localize the
    original current test-action restatement by avoiding a
    compact target support along the whole time interval.
    This supporting open-locus theorem uses the preceding
    compact-product tube lemma and original class-zero continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormClassOneUP NormOpenPreimage InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap EuclideanBlockNormTopology
  TopologicalProductMaps SmoothCompactSet CurrentCartesianDomain CurrentSegmentCompactSet
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CompactProductTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyAvoidCompact.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNT := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation TT := (real_norm_metric_space hNT).
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
Variable K:smooth_compact_set hNY V.

(** Source for [current_homotopy_avoid_compact]: the source
    points whose entire original time path misses a compact
    target support, supporting the compact replacements in
    Federer 4.1.9, p. 363. This deterministic locus
    introduces no chosen neighbourhood or support assumption. *)
Definition current_homotopy_avoid_compact:set X:=
  [set x|U x /\ forall a,smooth_compact_carrier KTime a->
    ~smooth_compact_carrier K (h (euclidean_block_join (a,x)))].

(** Source for [current_homotopy_avoid_compact_open]: compactness
    of the original time segment makes its whole-path avoidance
    locus open, supporting the test-action restatement in
    Federer 4.1.9, p. 363. Continuity is required only
    on the original open product domain. *)
Theorem current_homotopy_avoid_compact_open:
  norm_class_zero NZ NY AU h->@open XT current_homotopy_avoid_compact.
Proof.
move=>hContinuous.
pose O:set Z:=[set z|AU z /\~smooth_compact_carrier K (h z)].
have hClosed:@closed (real_norm_metric_space hNY) (smooth_compact_carrier K).
  exact:(compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) (smooth_compact_is_compact K)).
have hO:@open ZT O.
  exact:(@norm_class_zero_open_preimage R Z Y NZ NY hNZ hNY AU
    (~` smooth_compact_carrier K) h hContinuous (closed_openC hClosed)).
pose J (p:XT*TT):ZT:=euclidean_block_join (p.2,p.1).
have hSwap:continuous (fun p:XT*TT=>(p.2,p.1):(TT*XT)%type).
  exact:(topological_pair_continuous (@second_projection_continuous XT TT)
    (@first_projection_continuous XT TT)).
have hJ:continuous J.
  move=>p;exact:(continuous_comp (@hSwap p)
    (@euclidean_block_join_norm_continuous R 1%N n (p.2,p.1))).
have hPre:@open [the topologicalType of (XT*TT)%type] (J @^-1` O).
  exact:((@continuousP [the topologicalType of (XT*TT)%type] ZT J).1 hJ O hO).
have hOpenU:@open XT U.
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
rewrite openE=>x [hx hAvoid].
have hAt a:smooth_compact_carrier KTime a->(J @^-1` O) (x,a).
  move=>ha;split;last exact:(@hAvoid a ha).
  change (AT (@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).1 /\
    U (@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).2).
  rewrite euclidean_block_joinK;split;last exact:hx.
  exact:(smooth_compact_in_domain KTime a ha).
have[W [B [hW [hWx [hB [hKB hWB]]]]]]:=
  @compact_product_open_tube XT TT x (smooth_compact_carrier KTime) (J @^-1` O)
    (smooth_compact_is_compact KTime) hPre hAt.
apply:(filterS _ (@open_nbhs_nbhs XT x (W `&` U) (conj (openI hW hOpenU) (conj hWx hx)))).
move=>y [hy hu];split=>// a ha.
exact:(hWB (y,a) (conj hy (hKB a ha))).2.
Qed.
End CurrentHomotopyAvoidCompact.
