(** Federer (1969), 4.1.11, p. 365: factor the original
    p(x,t,y)=(y,1-t,x) through the preceding Cartesian swaps,
    time reflection and natural association. Their existing
    smoothness laws justify the original reversing pushforward. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianSwap EuclideanCartesianSwapLinear
  EuclideanDimensionCastLinear EuclideanCartesianReassociation
  CurrentCartesianMapClass CurrentJoinTimeReflection CurrentJoinSliceMapClass
  CurrentJoinReverseMapUP CurrentJoinReverseMapSealed CurrentJoinReverseMapLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_reverse_inner_map]: the original
    (t,y) maps to (y,1-t), as a composition of the preceding
    swap and product maps, supporting Federer 4.1.11, p. 365. *)
Definition current_join_reverse_inner_map (R:realType) n
    (z:R_n R (1+n)%N):R_n R (n+1)%N:=
  @euclidean_cartesian_map R n 1%N n 1%N (fun x:R_n R n=>x)
    (@current_join_time_reflection R) (@euclidean_cartesian_swap_map R 1%N n z).

(** Source for [current_join_reverse_middle_map]: apply the
    preceding (t,y) reversal beside the retained x factor,
    supporting the original p of Federer 4.1.11, p. 365. *)
Definition current_join_reverse_middle_map (R:realType) n:=
  @euclidean_cartesian_map R (1+n)%N n (n+1)%N n
    (@current_join_reverse_inner_map R n) (fun x:R_n R n=>x).

(** Source for [current_join_reverse_inner_coordinates]: the
    original middle step sends (t,y) exactly to (y,1-t),
    supporting the reversing map in Federer 4.1.11, p. 365. *)
Lemma current_join_reverse_inner_coordinates (R:realType) n t (y:R_n R n):
  @current_join_reverse_inner_map R n
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))=
  @euclidean_block_join R n 1%N (y,@euclidean_one_embed R (1-t)).
Proof.
rewrite /current_join_reverse_inner_map.
change (@euclidean_cartesian_map R n 1%N n 1%N (fun x:R_n R n=>x)
    (@current_join_time_reflection R)
    (@euclidean_cartesian_swap R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y)))=
    @euclidean_block_join R n 1%N (y,@euclidean_one_embed R (1-t))).
rewrite /euclidean_cartesian_swap euclidean_block_joinK.
by rewrite /euclidean_cartesian_map euclidean_block_joinK current_join_time_reflection_coordinates.
Qed.

(** Source for [current_join_reverse_middle_coordinates]: the
    middle product map acts on its two original blocks,
    supporting Federer 4.1.11, p. 365. This is the existing
    Cartesian product-map law, including empty spatial blocks. *)
Lemma current_join_reverse_middle_coordinates (R:realType) n
    (a:R_n R (1+n)%N) (x:R_n R n):
  @current_join_reverse_middle_map R n (@euclidean_block_join R (1+n)%N n (a,x))=
    @euclidean_block_join R (n+1)%N n (@current_join_reverse_inner_map R n a,x).
Proof. by rewrite /current_join_reverse_middle_map /euclidean_cartesian_map euclidean_block_joinK. Qed.

(** Source for [current_join_reverse_factorization]: the
    original p is the outer swap, the preceding middle map
    and the natural association, supporting the Cartesian
    anticommutativity argument in Federer 4.1.11, p. 365.
    Identify the sealed map by its independent coordinates. *)
Theorem current_join_reverse_factorization (R:realType) n:
  @CurrentJoinReverseMap.value R n=
  (fun z:R_n R (n+(1+n))%N=>
    @euclidean_dimension_cast_map R ((n+1)+n)%N (n+(1+n))%N (esym (addnA n 1%N n))
      (@current_join_reverse_middle_map R n (@euclidean_cartesian_swap_map R n (1+n)%N z))).
Proof.
apply:(@current_join_reverse_map_unique R n).
- exact:CurrentJoinReverseMap.laws.
- move=>x t y.
  have hOuter:@euclidean_cartesian_swap_map R n (1+n)%N
      (@euclidean_block_join R n (1+n)%N
        (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y)))=
    @euclidean_block_join R (1+n)%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y),x).
    change (@euclidean_cartesian_swap R n (1+n)%N
      (@euclidean_block_join R n (1+n)%N
        (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y)))=
      @euclidean_block_join R (1+n)%N n
        (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y),x)).
    by rewrite /euclidean_cartesian_swap euclidean_block_joinK.
  by rewrite hOuter current_join_reverse_middle_coordinates current_join_reverse_inner_coordinates
    euclidean_cartesian_reassociate_join.
Qed.

Section Smoothness.
Variable R:realType.
Variable n:nat.
Local Notation Full := (fun m=>fun _:R_n R m=>True).
Local Notation N := (fun m=>inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (fun m=>inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hFull := (fun m (x:R_n R m) (_:True)=>@norm_full_domain_interior R (R_n R m) (N m) x).
Local Notation Inner := (@current_join_reverse_inner_map R n).
Local Notation Middle := (@current_join_reverse_middle_map R n).
Local Notation Outer := (@euclidean_cartesian_swap_map R n (1+n)%N).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((n+1)+n)%N (n+(1+n))%N
  (esym (addnA n 1%N n))).

(** Source for [current_join_reverse_inner_smooth]: the
    original (t,y) reversal is globally smooth by the preceding
    swap, reflection and product calculus, supporting Federer
    4.1.11, p. 365. *)
Theorem current_join_reverse_inner_smooth:
  norm_class_all_orders (hN (1+n)%N) (hN (n+1)%N) (Full (1+n)%N) Inner.
Proof.
have hSwap:=@euclidean_cartesian_swap_smooth R 1%N n (Full (1+n)%N) (hFull (1+n)%N).
have hProduct:=@current_cartesian_map_smooth R n 1%N n 1%N
  (fun x:R_n R n=>x) (@current_join_time_reflection R)
  (@current_join_slice_identity_smooth R n)
  (@current_join_time_reflection_smooth R (Full 1%N) (hFull 1%N)).
move=>k.
exact:(@norm_class_compose_on R (R_n R (1+n)%N) (R_n R (n+1)%N) (R_n R (n+1)%N)
  (N (1+n)%N) (N (n+1)%N) (N (n+1)%N) (hN (1+n)%N) (hN (n+1)%N) (hN (n+1)%N)
  (Full (1+n)%N) (Full (n+1)%N) (@euclidean_cartesian_swap_map R 1%N n)
  (@euclidean_cartesian_map R n 1%N n 1%N (fun x:R_n R n=>x)
    (@current_join_time_reflection R)) k (fun _ _=>Logic.I) (hSwap k) (hProduct k)).
Qed.

(** Source for [current_join_reverse_middle_smooth]: the
    original middle product map is smooth by the preceding
    factor laws, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_middle_smooth:
  norm_class_all_orders (hN ((1+n)+n)%N) (hN ((n+1)+n)%N) (Full ((1+n)+n)%N) Middle.
Proof.
exact:(@current_cartesian_map_smooth R (1+n)%N n (n+1)%N n
  Inner (fun x:R_n R n=>x) current_join_reverse_inner_smooth
  (@current_join_slice_identity_smooth R n)).
Qed.

(** Source for [current_join_reverse_map_smooth]: the original
    opaque p is smooth on its Euclidean source, supporting the
    displayed reversing pushforward in Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_map_smooth:
  norm_class_all_orders (hN (n+(1+n))%N) (hN (n+(1+n))%N)
    (Full (n+(1+n))%N) (@CurrentJoinReverseMap.value R n).
Proof.
have hOuter:=@euclidean_cartesian_swap_smooth R n (1+n)%N
  (Full (n+(1+n))%N) (hFull (n+(1+n))%N).
have hAssoc:=@euclidean_dimension_cast_smooth R ((n+1)+n)%N (n+(1+n))%N
  (esym (addnA n 1%N n)) (Full ((n+1)+n)%N) (hFull ((n+1)+n)%N).
move=>k.
have hMiddle:=@norm_class_compose_on R (R_n R (n+(1+n))%N)
  (R_n R ((1+n)+n)%N) (R_n R ((n+1)+n)%N)
  (N (n+(1+n))%N) (N ((1+n)+n)%N) (N ((n+1)+n)%N)
  (hN (n+(1+n))%N) (hN ((1+n)+n)%N) (hN ((n+1)+n)%N)
  (Full (n+(1+n))%N) (Full ((1+n)+n)%N) Outer Middle k
  (fun _ _=>Logic.I) (hOuter k) (current_join_reverse_middle_smooth k).
have hComposite:=@norm_class_compose_on R (R_n R (n+(1+n))%N)
  (R_n R ((n+1)+n)%N) (R_n R (n+(1+n))%N)
  (N (n+(1+n))%N) (N ((n+1)+n)%N) (N (n+(1+n))%N)
  (hN (n+(1+n))%N) (hN ((n+1)+n)%N) (hN (n+(1+n))%N)
  (Full (n+(1+n))%N) (Full ((n+1)+n)%N) (fun z=>Middle (Outer z)) Assoc k
  (fun _ _=>Logic.I) hMiddle (hAssoc k).
apply:(norm_class_domain_agreement _ hComposite)=>z _.
by rewrite current_join_reverse_factorization.
Qed.

(** Source for [current_join_reverse_open_smooth]: restrict
    the same original p to any open source, supporting its
    original-domain pushforward in Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_open_smooth (W:set (R_n R (n+(1+n))%N))
    (hW:forall z,W z->norm_domain_interior (N (n+(1+n))%N) W z):
  norm_class_all_orders (hN (n+(1+n))%N) (hN (n+(1+n))%N) W
    (@CurrentJoinReverseMap.value R n).
Proof.
move=>k.
exact:(@norm_class_open_restriction R (R_n R (n+(1+n))%N) (R_n R (n+(1+n))%N)
  (N (n+(1+n))%N) (N (n+(1+n))%N) (hN (n+(1+n))%N) (hN (n+(1+n))%N)
  (Full (n+(1+n))%N) W (@CurrentJoinReverseMap.value R n) k
  (fun _ _=>Logic.I) hW (current_join_reverse_map_smooth k)).
Qed.
End Smoothness.
