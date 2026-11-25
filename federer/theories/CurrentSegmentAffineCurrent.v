(** Federer (1969), 4.1.11, pp. 365–366: the
    original segment is the affine current image of
    the positive unit interval. Align the public affine
    image interface with the already proved actual
    segment pushforward by map agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentSpaces CurrentSegmentMapUP OrientedSegmentCurrentSealed CurrentCartesianMapPullback
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinAffineSourcePushforward CurrentSegmentAffineMap CurrentSegmentAffinePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSegmentAffineCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables u v:R_n R n.
Local Notation A := (@current_segment_affine_map R n u v).
Local Notation hA := (@current_segment_affine_map_affine R n u v).
Local Notation GlobalClass := (@euclidean_affine_map_smooth R 1%N n (Full 1%N) (hFull 1%N) A hA).
Local Notation AffineClass := (@current_cartesian_factor_open_class R 1%N n
  (Full 1%N) (hFull 1%N) A GlobalClass).
Local Notation SegmentClass := (@current_segment_affine_map_smooth R n u v (Full 1%N) (hFull 1%N)).
Local Notation Image := (fun (z:R_n R 1%N) (_:True)=>Logic.I).
Local Notation ICurrent := (@current_join_time_segment R h2).
Local Notation hICurrent := (@current_join_time_segment_compact R h2).

(** Source for [current_segment_affine_current]: the
    actual affine image of [0,1] is the original
    [u,v], supporting the arbitrary prism factors in
    Federer 4.1.11, p. 366. The preceding exact
    segment action of p. 365 is reused, with
    coincident endpoints and dimension zero retained. *)
Theorem current_segment_affine_current (hUV:@is_current_segment_domain R n (Full n) u v):
  @current_join_affine_current R h2 1%N n A hA 1%N ICurrent hICurrent=
  @OrientedSegmentCurrent.value R h2 n (Full n) (hFull n) u v hUV.
Proof.
have hCompare:=@current_compact_map_images_agree R h2 1%N n
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) A Image AffineClass 1%N ICurrent hICurrent
  A Image SegmentClass hICurrent (fun _ _=>erefl).
exact:(eq_trans hCompare (@current_segment_affine_pushforward R h2 n u v hUV)).
Qed.
End CurrentSegmentAffineCurrent.
