(** Federer (1969), 4.1.13, p. 369: the original compact
    set C is the union of affine segments over spt T.
    Its exact set formula is independent of the chosen
    open neighbourhood used later in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentCartesianCompact CurrentSegmentCompactSet
  ScalarSegmentCoordinateValues ConvexMetricSegment
  CurrentSpaces SmoothCompactSet SmoothCompactImage
  CurrentHomotopyUP
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed CurrentAffineHomotopyClass
  CurrentSegmentMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineSegmentHull.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables f g:X->Y.
Variable T:@current_space R h2 n U hU m.
Local Notation support := (@current_support R h2 n U hU m T).

(** Source for [current_affine_segment_hull]: exactly the set
    C={(1-t)f(x)+tg(x):x in spt T,0<=t<=1} in
    Federer 4.1.13, p. 369. *)
Definition current_affine_segment_hull:set Y:=
  [set y|exists (t:R) (x:X),0<=t<=1 /\support x /\(1-t)*:f x+t*:g x=y].

Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).
Local Notation Full := (fun _:R=>True).
Local Notation Target := (fun _:Y=>True).
Local Notation FullU := (@current_homotopy_product_domain R n Full U).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
(** The cylinder is the literal point-set product over the
    original support. Its compactness proof uses that support
    directly; openness evidence is not a premise of this set. *)
Local Notation cylinder := ([set z:Z|
  0<=@euclidean_one_project R (p z)<=1 /\support (q z)]).

(** Source for [current_affine_segment_hull_image]: the original
    C is exactly the affine image of [0,1] times spt T,
    supporting Federer 4.1.13, pp. 369–370. Only
    the public affine law and the original block inverses are used. *)
Theorem current_affine_segment_hull_image:
  H @` cylinder=current_affine_segment_hull.
Proof.
apply/seteqP;split.
- move=>y [z [ht hx] <-].
  exists (@euclidean_one_project R (p z)),(q z);split;first exact:ht.
  split;first exact:hx.
  apply:esym;exact:current_affine_homotopy_coordinates.
- move=>y [t [x [ht [hx <-]]]].
  pose z:=@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x).
  have hp:p z=@euclidean_one_embed R t:=
    congr1 fst (@euclidean_block_joinK R 1%N n (@euclidean_one_embed R t,x)).
  have hq:q z=x:=
    congr1 snd (@euclidean_block_joinK R 1%N n (@euclidean_one_embed R t,x)).
  exists z.
  + change (0<=@euclidean_one_project R (p z)<=1 /\support (q z)).
    by rewrite hp hq euclidean_one_embedK.
  + exact:CurrentAffineHomotopy.laws.
Qed.

(** Source for [current_affine_segment_hull_compact]: the exact
    original C is compact for a compactly supported T,
    supporting the flat seminorm in Federer 4.1.13,
    p. 369. The proof uses a compact cylinder and the
    already proved smooth compact-image theorem. *)
Theorem current_affine_segment_hull_compact:
  @compact (real_norm_metric_space hNX) support->
  @compact (real_norm_metric_space hNY) current_affine_segment_hull.
Proof.
move=>hCompact.
pose u:=@euclidean_one_embed R 0.
pose v:=@euclidean_one_embed R 1.
pose hSegment:=@scalar_segment_full_domain R 0 1.
pose KTime:=@current_segment_compact_set R 1%N (fun _=>True) u v hSegment.
have hBand a:smooth_compact_carrier KTime a<->0<=@euclidean_one_project R a<=1.
  split.
  - move=>ha;have[t [ht ->]]:=@current_segment_compact_points R 1%N
      (fun _=>True) u v hSegment a ha.
    rewrite /u /v scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
    by move:ht;rewrite in_itv /=.
  - move=>ha.
    have hTime:(@euclidean_one_project R a) \in (`[0,1])%R by rewrite in_itv /=.
    have hPoint:=@current_segment_point_in_compact R 1%N (fun _=>True)
      u v hSegment (@euclidean_one_project R a) hTime.
    by rewrite /u /v scalar_segment_parameter_value subr0 mul1r addr0
      euclidean_one_projectK in hPoint.
have hCylinderEqual:cylinder=@euclidean_cartesian_set R 1%N n
    (smooth_compact_carrier KTime) support.
  apply:funext=>z;apply:propext.
  change ((0<=@euclidean_one_project R (p z)<=1 /\support (q z))<->
    (smooth_compact_carrier KTime (p z) /\support (q z))).
  split;move=>[ht hx];split=>//;exact:(hBand _).2 ht || exact:(hBand _).1 ht.
have hCylinderCompact:@compact (real_norm_metric_space hNZ) cylinder.
  rewrite hCylinderEqual.
  exact:(@current_cartesian_compact R 1%N n (smooth_compact_carrier KTime)
    support (smooth_compact_is_compact KTime) hCompact).
have hCylinderDomain:cylinder `<=` FullU.
  move=>z [ht hx];split;first exact:Logic.I.
  exact:hx.1.
pose K:=@Build_smooth_compact_set R Z NZ hNZ FullU cylinder
  hCylinderDomain hCylinderCompact.
have hInterval:@is_homotopy_parameter_interval R Full.
  constructor;first exact:openT;by [].
have hSmooth:=@current_affine_homotopy_smooth R n nu f g Full hInterval
  U hU hf hg.
pose image:=@smooth_compact_image R Z Y NZ NY hNZ hNY FullU Target H
  (fun z hz=>Logic.I) (norm_class_continuous (hSmooth 0%N)) K.
have hImage:=smooth_compact_is_compact image.
change (@compact (real_norm_metric_space hNY) (H @` cylinder)) in hImage.
by rewrite current_affine_segment_hull_image in hImage.
Qed.
End CurrentAffineSegmentHull.
