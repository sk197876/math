(** Federer (1969), 4.1.11, p. 366: the
    two original iterated join maps on their ordered
    five-factor source. Reuse the literal F and the
    preceding canonical block maps; only the left
    grouping needs an equal-dimension identification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCoordinateLists EuclideanDimensionCastLinear EuclideanCartesianMap
  CurrentCartesianMapClass CurrentJoinSliceMapClass CurrentJoinMapSealed CurrentJoinMapClass
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_assoc_left_dimension]: the
    original ordered coordinate dimensions agree under
    the left grouping, supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_dimension n:
  (n+(1+(n+(1+n))))%N=((n+(1+n))+(1+n))%N.
Proof. by rewrite !addnA. Qed.

Section CurrentJoinAssociativityIteratedMaps.
Variable R:realType.
Variable n:nat.
Local Notation d := ((n+(1+(n+(1+n))))%N).
Local Notation leftd := (((n+(1+n))+(1+n))%N).
Local Notation joind := ((n+(1+n))%N).
Local Notation Full := (fun k:nat=>fun _:R_n R k=>True).
Local Notation hFull := (fun (k:nat) (x:R_n R k) (_:True)=>
  @norm_full_domain_interior R (R_n R k) (inner_norm (@euclidean_inner_productP R k)) x).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation hF := (@current_join_map_smooth R n (Full joind) (hFull joind)).
Local Notation Id := (fun k:nat=>fun x:R_n R k=>x).
Local Notation hId := (@current_join_slice_identity_smooth R).

(** Source for [current_join_assoc_left_regroup]: identify the
    original (x,a,y,b,z) source with ((x,a,y),b,z),
    supporting the left iterated join in Federer
    4.1.11, p. 366. *)
Definition current_join_assoc_left_regroup:Hom (R_n R d) (R_n R leftd):=
  @euclidean_dimension_cast_map R d leftd (current_join_assoc_left_dimension n).

(** Source for [current_join_assoc_left_map]: the original
    F(F(x,a,y),b,z) on the ordered five factors,
    supporting Federer 4.1.11, p. 366. *)
Definition current_join_assoc_left_map (p:R_n R d):R_n R n:=
  F (@euclidean_cartesian_map R joind (1+n)%N n (1+n)%N
    F (Id (1+n)%N) (current_join_assoc_left_regroup p)).

(** Source for [current_join_assoc_right_map]: the original
    F(x,a,F(y,b,z)) on the same ordered five factors,
    supporting Federer 4.1.11, p. 366. *)
Definition current_join_assoc_right_map (p:R_n R d):R_n R n:=
  F (@euclidean_cartesian_map R n (1+joind)%N n (1+n)%N (Id n)
    (@euclidean_cartesian_map R 1%N joind 1%N n (Id 1%N) F) p).

(** Source for [current_join_assoc_left_regroup_coordinates]: the
    original five ordered coordinate lists are unchanged
    by the left grouping, supporting Federer 4.1.11,
    p. 366, including empty spatial factors. *)
Lemma current_join_assoc_left_regroup_coordinates (x y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_left_regroup (@euclidean_block_join R n (1+joind)%N
    (x,@euclidean_block_join R 1%N joind
      (a,@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z)))))=
  @euclidean_block_join R joind (1+n)%N
    (@euclidean_block_join R n (1+n)%N (x,@euclidean_block_join R 1%N n (a,y)),
      @euclidean_block_join R 1%N n (b,z)).
Proof.
apply:(@euclidean_coordinate_list_injective R leftd).
rewrite /current_join_assoc_left_regroup /euclidean_dimension_cast_map
  euclidean_dimension_cast_list !euclidean_block_join_list;cbn beta iota.
by rewrite !catA.
Qed.

(** Source for [current_join_assoc_left_map_coordinates]: the
    canonical left map has the literal first printed
    iterated F value, Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_map_coordinates (x y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_left_map (@euclidean_block_join R n (1+joind)%N
    (x,@euclidean_block_join R 1%N joind
      (a,@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z)))))=
  F (@euclidean_block_join R n (1+n)%N
    (F (@euclidean_block_join R n (1+n)%N (x,@euclidean_block_join R 1%N n (a,y))),
      @euclidean_block_join R 1%N n (b,z))).
Proof.
rewrite /current_join_assoc_left_map current_join_assoc_left_regroup_coordinates
  /euclidean_cartesian_map euclidean_block_joinK.
by [].
Qed.

(** Source for [current_join_assoc_right_map_coordinates]: the
    canonical right map has the literal second printed
    iterated F value, Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_right_map_coordinates (x y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_right_map (@euclidean_block_join R n (1+joind)%N
    (x,@euclidean_block_join R 1%N joind
      (a,@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z)))))=
  F (@euclidean_block_join R n (1+n)%N
    (x,@euclidean_block_join R 1%N n
      (a,F (@euclidean_block_join R n (1+n)%N (y,@euclidean_block_join R 1%N n (b,z)))))).
Proof.
rewrite /current_join_assoc_right_map /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
rewrite /euclidean_cartesian_map euclidean_block_joinK.
by [].
Qed.

(** Source for [current_join_assoc_left_map_smooth]: the original
    left iterated F map is smooth by the preceding
    product and composition calculus, supporting Federer
    4.1.11, p. 366. *)
Lemma current_join_assoc_left_map_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R d))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full d) current_join_assoc_left_map.
Proof.
pose AClass:=@euclidean_dimension_cast_smooth R d leftd (current_join_assoc_left_dimension n)
  (Full d) (hFull d).
pose B:=@euclidean_cartesian_map R joind (1+n)%N n (1+n)%N F (Id (1+n)%N).
pose BClass:=@current_cartesian_map_smooth R joind (1+n)%N n (1+n)%N F (Id (1+n)%N) hF (hId (1+n)%N).
pose FirstClass:=@current_smooth_composite_class R d leftd joind (Full d) (Full leftd)
  current_join_assoc_left_regroup B (fun _ _=>Logic.I) AClass BClass.
exact:(@current_smooth_composite_class R d joind n (Full d) (Full joind)
  (fun p=>B (current_join_assoc_left_regroup p)) F (fun _ _=>Logic.I) FirstClass hF).
Qed.

(** Source for [current_join_assoc_right_map_smooth]: the original
    right iterated F map is smooth by the same
    actual Cartesian and composition calculus, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_right_map_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R d))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full d) current_join_assoc_right_map.
Proof.
pose Inner:=@euclidean_cartesian_map R 1%N joind 1%N n (Id 1%N) F.
pose InnerClass:=@current_cartesian_map_smooth R 1%N joind 1%N n (Id 1%N) F (hId 1%N) hF.
pose Middle:=@euclidean_cartesian_map R n (1+joind)%N n (1+n)%N (Id n) Inner.
pose MiddleClass:=@current_cartesian_map_smooth R n (1+joind)%N n (1+n)%N
  (Id n) Inner (hId n) InnerClass.
exact:(@current_smooth_composite_class R d joind n (Full d) (Full joind)
  Middle F (fun _ _=>Logic.I) MiddleClass hF).
Qed.
End CurrentJoinAssociativityIteratedMaps.
