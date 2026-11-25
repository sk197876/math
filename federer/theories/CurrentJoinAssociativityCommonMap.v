(** Federer (1969), 4.1.11, p. 366: retain
    the original H after identifying the common image
    order (x,y,w,z) with (x,y,z,w). The common
    square maps retain their original coordinate values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanCartesianMap CurrentJoinAssociatorMapsSealed CurrentJoinBarycentreClass
  CurrentJoinAssociativityRegroup CurrentJoinAssociativityRegroupClass
  CurrentJoinAssociativitySquareSlot SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_assoc_weighted_map]: the
    original H applied to the common image factors,
    supporting Federer 4.1.11, p. 366. This is a
    composite of preceding maps, not a replacement H. *)
Definition current_join_assoc_weighted_map (R:realType) n
    (p:R_n R (n+(n+(3+n)))%N):R_n R n:=
  @CurrentJoinAssociatorMaps.barycentre R n (@current_join_assoc_weight_regroup R n p).

(** Source for [current_join_assoc_weighted_map_smooth]: the
    original common H map is smooth by the preceding
    block and H laws, supporting Federer 4.1.11,
    p. 366. *)
Lemma current_join_assoc_weighted_map_smooth (R:realType) n:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(3+n)))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True)
    (@current_join_assoc_weighted_map R n).
Proof.
exact:(@current_smooth_composite_class R (n+(n+(3+n)))%N (n+(n+(n+3)))%N n
  (fun _=>True) (fun _=>True) (@current_join_assoc_weight_regroup R n)
  (@CurrentJoinAssociatorMaps.barycentre R n) (fun _ _=>Logic.I)
  (@current_join_assoc_weight_regroup_smooth R n) (@current_join_barycentre_smooth R n)).
Qed.

(** Source for [current_join_assoc_weighted_map_coordinates]: the
    common image map has exactly Federer's original
    H input (x,y,z,w), supporting 4.1.11, p. 366. *)
Lemma current_join_assoc_weighted_map_coordinates (R:realType) n
    (x y z:R_n R n) (w:R_n R 3%N):
  @current_join_assoc_weighted_map R n (@euclidean_block_join R n (n+(3+n))%N
    (x,@euclidean_block_join R n (3+n)%N (y,@euclidean_block_join R 3%N n (w,z))))=
  @CurrentJoinAssociatorMaps.barycentre R n (@euclidean_block_join R n (n+(n+3))%N
    (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_block_join R n 3%N (z,w)))).
Proof. by rewrite /current_join_assoc_weighted_map current_join_assoc_weight_coordinates. Qed.

(** Source for [current_join_assoc_square_slot_coordinates]: the
    square map acts only on its original time pair,
    retaining x,y,z, supporting Federer 4.1.11, p. 366.
    This value law itself needs no smoothness hypothesis. *)
Lemma current_join_assoc_square_slot_coordinates (R:realType) n
    (h:R_n R 2%N->R_n R 3%N) (x y z:R_n R n) (t:R_n R 2%N):
  @current_join_assoc_square_slot R n h (@euclidean_block_join R n (n+(2+n))%N
    (x,@euclidean_block_join R n (2+n)%N (y,@euclidean_block_join R 2%N n (t,z))))=
  @euclidean_block_join R n (n+(3+n))%N
    (x,@euclidean_block_join R n (3+n)%N (y,@euclidean_block_join R 3%N n (h t,z))).
Proof.
rewrite /current_join_assoc_square_slot /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
rewrite /current_join_assoc_square_middle /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
rewrite /current_join_assoc_square_inner /euclidean_cartesian_map euclidean_block_joinK.
by [].
Qed.
