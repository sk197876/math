(** Federer (1969), 4.1.11, p. 366: the
    original time-factor reorderings use the preceding
    Cartesian interchanges and natural associations. This
    is their canonical composite linear map, not a new
    chosen Cartesian structure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormOpenDomainLaws NormFiniteLinearBound
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanCartesianLinear EuclideanCartesianSwap EuclideanCartesianSwapLinear
  EuclideanDimensionCastLinear EuclideanCartesianReassociation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_first_two_block_interchange]: the
    original identification (x,y,z) mapped to (y,x,z),
    supporting the time-space reordering in Federer
    4.1.11, p. 366. Only preceding linear block
    maps, swaps and associations are composed. *)
Definition current_first_two_block_interchange (R:realType) m n v:
    Hom (R_n R (m+(n+v))%N) (R_n R (n+(m+v))%N):=
  hom_comp (@euclidean_cartesian_linear R n (v+m)%N n (m+v)%N
    (hom_of_linear (@linear_id R (R_n R n))) (@euclidean_cartesian_swap_map R v m))
    (hom_comp (@euclidean_dimension_cast_map R ((n+v)+m)%N (n+(v+m))%N (esym (addnA n v m)))
      (@euclidean_cartesian_swap_map R m (n+v)%N)).

(** Source for [current_first_two_block_coordinates]: the
    canonical composite has exactly the original ordered
    block values (y,x,z), supporting Federer 4.1.11,
    p. 366, including empty blocks. *)
Lemma current_first_two_block_coordinates (R:realType) m n v
    (x:R_n R m) (y:R_n R n) (z:R_n R v):
  @current_first_two_block_interchange R m n v
    (@euclidean_block_join R m (n+v)%N (x,@euclidean_block_join R n v (y,z)))=
  @euclidean_block_join R n (m+v)%N (y,@euclidean_block_join R m v (x,z)).
Proof.
rewrite /current_first_two_block_interchange !hom_compE euclidean_cartesian_linearE.
have hOuter:@euclidean_cartesian_swap_map R m (n+v)%N
    (@euclidean_block_join R m (n+v)%N (x,@euclidean_block_join R n v (y,z)))=
    @euclidean_block_join R (n+v)%N m (@euclidean_block_join R n v (y,z),x).
  change (@euclidean_cartesian_swap R m (n+v)%N
    (@euclidean_block_join R m (n+v)%N (x,@euclidean_block_join R n v (y,z)))=
    @euclidean_block_join R (n+v)%N m (@euclidean_block_join R n v (y,z),x)).
  by rewrite /euclidean_cartesian_swap euclidean_block_joinK.
rewrite hOuter euclidean_cartesian_reassociate_join /euclidean_cartesian_map euclidean_block_joinK.
change (@euclidean_block_join R n (m+v)%N
    (y,@euclidean_cartesian_swap R v m (@euclidean_block_join R v m (z,x)))=
  @euclidean_block_join R n (m+v)%N (y,@euclidean_block_join R m v (x,z))).
by rewrite /euclidean_cartesian_swap euclidean_block_joinK.
Qed.

(** Source for [current_first_two_block_smooth]: the
    same original block identification is smooth by
    bounded finite-dimensional linear calculus, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_first_two_block_smooth (R:realType) m n v:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (m+(n+v))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(m+v))%N))
    (fun _=>True) (@current_first_two_block_interchange R m n v).
Proof.
move=>k.
apply:(@norm_class_linear R (R_n R (m+(n+v))%N) (R_n R (n+(m+v))%N) _ _
  (inner_norm_real_norm (@euclidean_inner_productP R (m+(n+v))%N))
  (inner_norm_real_norm (@euclidean_inner_productP R (n+(m+v))%N))
  (fun _=>True) (@current_first_two_block_interchange R m n v) k).
- move=>x _;exact:norm_full_domain_interior.
- exact:(@norm_finite_linear_bounded R (R_n R (m+(n+v))%N) (R_n R (n+(m+v))%N) _ _
    (inner_norm_real_norm (@euclidean_inner_productP R (m+(n+v))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(m+v))%N))
    (m+(n+v))%N (@coordinate_basis R (m+(n+v))%N) (@coordinate_basisP R (m+(n+v))%N)
    (@current_first_two_block_interchange R m n v)).
Qed.
