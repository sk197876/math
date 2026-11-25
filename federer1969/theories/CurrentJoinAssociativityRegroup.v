(** Federer (1969), 4.1.11, p. 366: the
    original common square and spatial factors are
    regrouped by the preceding canonical linear block
    identifications. These aliases choose no new product
    or current structure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP AffineMaps RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianLinear EuclideanCartesianSwap
  EuclideanCartesianSwapLinear EuclideanDimensionCastLinear EuclideanCartesianReassociation
  CurrentFirstTwoBlockInterchange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityRegroup.
Variable R:realType.
Variable n:nat.
Local Notation Id := (hom_of_linear (@linear_id R (R_n R n))).
Local Notation FirstAssociation := (@euclidean_dimension_cast_map R ((1+1)+n)%N (1+(1+n))%N
  (esym (addnA 1%N 1%N n))).

(** Source for [current_join_assoc_inner_association]: identify
    y times ((a times b) times z) with
    y times (a times (b times z)), supporting
    Federer 4.1.11, p. 366. *)
Definition current_join_assoc_inner_association:
    Hom (R_n R (n+(2+n))%N) (R_n R (n+(1+(1+n)))%N):=
  @euclidean_cartesian_linear R n (2+n)%N n (1+(1+n))%N Id FirstAssociation.

(** Source for [current_join_assoc_inner_regroup]: the original
    inner coordinate order (y,a,b,z) becomes (a,y,b,z),
    supporting the common time-square argument in Federer
    4.1.11, p. 366. *)
Definition current_join_assoc_inner_regroup:
    Hom (R_n R (n+(2+n))%N) (R_n R (1+(n+(1+n)))%N):=
  hom_comp (@current_first_two_block_interchange R n 1%N (1+n)%N)
    current_join_assoc_inner_association.

(** Source for [current_join_assoc_common_regroup]: the original
    common source (x,y,a,b,z) becomes (x,a,y,b,z),
    supporting both compositions in Federer 4.1.11,
    p. 366. The preceding inner map is retained
    beside the original first spatial factor. *)
Definition current_join_assoc_common_regroup:
    Hom (R_n R (n+(n+(2+n)))%N) (R_n R (n+(1+(n+(1+n))))%N):=
  @euclidean_cartesian_linear R n (n+(2+n))%N n (1+(n+(1+n)))%N
    Id current_join_assoc_inner_regroup.

(** Source for [current_join_assoc_weight_regroup]: the common
    image order (x,y,w,z) becomes Federer's original
    H order (x,y,z,w), supporting 4.1.11, p. 366. *)
Definition current_join_assoc_weight_regroup:
    Hom (R_n R (n+(n+(3+n)))%N) (R_n R (n+(n+(n+3)))%N):=
  @euclidean_cartesian_linear R n (n+(3+n))%N n (n+(n+3))%N Id
    (@euclidean_cartesian_linear R n (3+n)%N n (n+3)%N Id (@euclidean_cartesian_swap_map R 3%N n)).

(** Source for [current_join_assoc_inner_coordinates]: the
    inner original block map has exactly the specified
    order (a,y,b,z), supporting Federer 4.1.11,
    p. 366. Empty spatial blocks are retained. *)
Lemma current_join_assoc_inner_coordinates (y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_inner_regroup (@euclidean_block_join R n (2+n)%N
    (y,@euclidean_block_join R 2%N n (@euclidean_block_join R 1%N 1%N (a,b),z)))=
  @euclidean_block_join R 1%N (n+(1+n))%N
    (a,@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z))).
Proof.
rewrite /current_join_assoc_inner_regroup hom_compE /current_join_assoc_inner_association
  euclidean_cartesian_linearE /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
rewrite euclidean_cartesian_reassociate_join.
exact:current_first_two_block_coordinates.
Qed.

(** Source for [current_join_assoc_common_coordinates]: both
    original parameters retain their order in the full
    common-source identification, supporting Federer 4.1.11,
    p. 366. *)
Lemma current_join_assoc_common_coordinates (x y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_common_regroup (@euclidean_block_join R n (n+(2+n))%N
    (x,@euclidean_block_join R n (2+n)%N
      (y,@euclidean_block_join R 2%N n (@euclidean_block_join R 1%N 1%N (a,b),z))))=
  @euclidean_block_join R n (1+(n+(1+n)))%N
    (x,@euclidean_block_join R 1%N (n+(1+n))%N
      (a,@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z)))).
Proof.
rewrite /current_join_assoc_common_regroup euclidean_cartesian_linearE
  /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
by rewrite current_join_assoc_inner_coordinates.
Qed.

(** Source for [current_join_assoc_weight_coordinates]: the
    common image maps to the literal original H input,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_weight_coordinates (x y z:R_n R n) (w:R_n R 3%N):
  current_join_assoc_weight_regroup (@euclidean_block_join R n (n+(3+n))%N
    (x,@euclidean_block_join R n (3+n)%N (y,@euclidean_block_join R 3%N n (w,z))))=
  @euclidean_block_join R n (n+(n+3))%N
    (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_block_join R n 3%N (z,w))).
Proof.
rewrite /current_join_assoc_weight_regroup euclidean_cartesian_linearE
  /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
rewrite euclidean_cartesian_linearE /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
change (@euclidean_block_join R n (n+(n+3))%N
  (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_cartesian_swap R 3%N n
    (@euclidean_block_join R 3%N n (w,z))))=
  @euclidean_block_join R n (n+(n+3))%N
    (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_block_join R n 3%N (z,w)))).
by rewrite /euclidean_cartesian_swap euclidean_block_joinK.
Qed.
End CurrentJoinAssociativityRegroup.
