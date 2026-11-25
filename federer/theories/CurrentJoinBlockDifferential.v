(** Federer (1969), 4.1.11, p. 365: evaluate the
    actual join differential on the original ordered
    x,t,y directions before passing to exterior powers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanScalarCoordinateMaps CurrentMapDifferential CurrentJoinMapSealed
  CurrentJoinMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinBlockDifferential.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation first := (@euclidean_first_block_map R n (1+n)%N).
Local Notation rest := (@euclidean_last_block_map R n (1+n)%N).
Local Notation middle := (hom_comp (@euclidean_first_block_map R 1%N n) rest).
Local Notation last := (hom_comp (@euclidean_last_block_map R 1%N n) rest).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) middle).
Local Notation Point a s b := (@euclidean_block_join R n (1+n)%N
  (a,@euclidean_block_join R 1%N n (@euclidean_one_embed R s,b))).
Variable U:set Z.
Hypothesis hU:forall z,U z->norm_domain_interior NZ U z.

(** Source for [current_join_map_block_differential]: the
    original three block directions have image
    (1-t)a+s(y-x)+tb under DF, supporting the first
    displayed mass estimate in Federer 4.1.11, p. 365. *)
Theorem current_join_map_block_differential z:U z->forall a s b,
  @current_map_differential R (n+(1+n))%N n U (@CurrentJoinMap.value R n) z (Point a s b)=
    (1-time z)*:a+s*:(last z-first z)+time z*:b.
Proof.
move=>hz a s b.
rewrite (@current_join_map_differential_value R n U hU z hz (Point a s b)).
change ((1-time z)*:(@euclidean_block_split R n (1+n)%N (Point a s b)).1+
  @euclidean_one_project R (@euclidean_block_split R 1%N n
    (@euclidean_block_split R n (1+n)%N (Point a s b)).2).1*:(last z-first z)+
  time z*:(@euclidean_block_split R 1%N n
    (@euclidean_block_split R n (1+n)%N (Point a s b)).2).2=
  (1-time z)*:a+s*:(last z-first z)+time z*:b).
by rewrite !euclidean_block_joinK euclidean_one_embedK.
Qed.
End CurrentJoinBlockDifferential.
