(** Federer (1969), 4.1.10, p. 364: the cone's support
    lies in the segments from u to spt T. Their union is compact
    and lies in U when U has the printed star-shaped property.
    Reuse the preceding closed-cylinder compactness, actual affine
    map, compact-image index and proper-pushforward support law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  CurrentSpaces SmoothCompactSet SmoothCompactImage CurrentHomotopyUP
  CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopyCompactCylinder
  CurrentDeformationChainSupport CurrentConeHomotopySealed CurrentConeHomotopyClass
  CurrentAmbientCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_current_star_shaped]: the original open U
    contains u and every segment from u to any of its points,
    Federer 4.1.10, p. 364, final mathematical paragraph. Openness
    is a separate premise; convexity is not imposed. *)
Record is_current_star_shaped (R:realType) n (U:set (R_n R n)) (u:R_n R n) : Prop := {
  (** Source for [current_star_shaped_centre]: u belongs to U,
      Federer 4.1.10, p. 364, final mathematical paragraph. *)
  current_star_shaped_centre : U u;
  (** Source for [current_star_shaped_segment]: all points of
      every original closed segment [u,x] stay in U, Federer
      4.1.10, p. 364, final mathematical paragraph. *)
  current_star_shaped_segment : forall (x:R_n R n) (t:R),
    U x -> 0<=t<=1 -> U ((1-t)*:u+t*:x)
}.

Section CurrentConeSegmentHull.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variable U : set X.
Hypothesis hOpen : forall x, U x -> norm_domain_interior NX U x.
Variable u : X.
Local Notation V := (fun _:X => True).
Local Notation A := (fun _:R => True).
Local Notation f := (fun _:X => u).
Local Notation g := (fun x:X => x).
Local Notation h := (@CurrentConeHomotopy.value R n u).
Local Notation hH := (@current_cone_ambient_homotopy R n u U hOpen).
Local Notation hU := (@current_homotopy_source_open R n n A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n n A U V f g h hH.1).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Variable T : @current_space R h2 n U hU j.
Local Notation support := (@current_support R h2 n U hU j T).
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n n j A U V f g h hH.1 T).

(** Source for [current_cone_segment_hull]: the original union
    of segments from u to spt T, supporting the compact-current
    conclusions in Federer 4.1.10, p. 364. Its affine formula is
    independent of a choice of homotopy map. *)
Definition current_cone_segment_hull : set X :=
  [set y | exists (t:R) (x:X), 0<=t<=1 /\ support x /\ (1-t)*:u+t*:x=y].

(** Source for [current_cone_segment_hull_image]: the original
    segment union is precisely h([0,1] times spt T), supporting
    Federer 4.1.10, p. 364. The affine map is used only through
    its sealed public formula and both original block inverse laws. *)
Theorem current_cone_segment_hull_image : h @` cylinder=current_cone_segment_hull.
Proof.
apply/seteqP; split.
- move=> y [z [ht hx] <-].
  exists (@euclidean_one_project R (p z)), (q z); split; first exact: ht.
  split; first exact: hx.
  apply: esym; exact: current_cone_homotopy_coordinates.
- move=> y [t [x [ht [hx <-]]]].
  pose z := @euclidean_block_join R 1%N n (@euclidean_one_embed R t,x).
  have hp : p z=@euclidean_one_embed R t :=
    congr1 fst (@euclidean_block_joinK R 1%N n (@euclidean_one_embed R t,x)).
  have hq : q z=x :=
    congr1 snd (@euclidean_block_joinK R 1%N n (@euclidean_one_embed R t,x)).
  exists z.
  + change (0<=@euclidean_one_project R (p z)<=1 /\ support (q z)).
    by rewrite hp hq euclidean_one_embedK.
  + exact: CurrentConeHomotopy.laws.
Qed.

(** Source for [current_cone_segment_hull_in_domain]: the whole
    original segment union lies in U under exactly its printed
    star-shaped hypothesis, Federer 4.1.10, p. 364. *)
Theorem current_cone_segment_hull_in_domain :
  is_current_star_shaped U u -> current_cone_segment_hull `<=` U.
Proof.
move=> hStar y [t [x [ht [hx <-]]]].
exact: (@current_star_shaped_segment R n U u hStar x t hx.1 ht).
Qed.

Hypothesis hCompact : @compact (real_norm_metric_space hNX) support.
Local Notation hProper := (@current_homotopy_compact_support_proper R h2 n n j
  A U V f g h hH T hCompact).

(** Source for [current_cone_segment_hull_compact]: the original
    cone-support segment union is compact, supporting Federer
    4.1.10, p. 364. Its compactness follows from the already
    proved compact cylinder and actual smooth compact-image law. *)
Theorem current_cone_segment_hull_compact :
  @compact (real_norm_metric_space hNX) current_cone_segment_hull.
Proof.
pose K := @Build_smooth_compact_set R Z NZ hNZ AU cylinder
  (@current_homotopy_cylinder_in_domain R h2 n n j A U V f g h hH.1 T)
  (@current_homotopy_compact_cylinder R h2 n n j A U V f g h hH T hCompact).
pose image := @smooth_compact_image R Z X NZ NX hNZ hNX AU V h
  (@current_homotopy_image R n n A U V f g h hH.1)
  (norm_class_continuous (hH.2 0%N)) K.
have hImage := smooth_compact_is_compact image.
change (@compact (real_norm_metric_space hNX) (h @` cylinder)) in hImage.
by rewrite current_cone_segment_hull_image in hImage.
Qed.

(** Source for [current_ambient_cone_support]: the original
    cone support lies in the exact segment union from u to spt T,
    supporting Federer 4.1.10, p. 364. This is the preceding
    proper homotopy support theorem, with no measure hypothesis. *)
Theorem current_ambient_cone_support :
  @current_support R h2 n V hV (1+j)%N
    (@current_ambient_cone R h2 n j U hOpen u T hCompact)
    `<=` current_cone_segment_hull.
Proof.
rewrite -current_cone_segment_hull_image.
exact: (@current_deformation_chain_support R h2 n n j A U V f g h hH T hProper).
Qed.
End CurrentConeSegmentHull.
