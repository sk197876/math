(** Federer (1969), 4.1.11, p. 366: the
    left join's original source and the ordered five
    factors differ only by two natural Cartesian
    associations. Reuse those maps and their original inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanCartesianMap EuclideanDimensionCastLinear EuclideanCartesianReassociation CurrentCartesianMapClass
  CurrentJoinSliceMapClass CurrentJoinAssociativityIteratedMaps SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityLeftSourceMaps.
Variable R:realType.
Variable n:nat.
Local Notation dj := ((n+(1+n))%N).
Local Notation dl := ((dj+(1+n))%N).
Local Notation dm := ((n+((1+n)+(1+n)))%N).
Local Notation df := ((n+(1+dj))%N).
Local Notation Full := (fun k:nat=>fun _:R_n R k=>True).
Local Notation hFull := (fun (k:nat) (x:R_n R k) (_:True)=>
  @norm_full_domain_interior R (R_n R k) (inner_norm (@euclidean_inner_productP R k)) x).
Local Notation First := (@euclidean_dimension_cast_map R dl dm (esym (addnA n (1+n)%N (1+n)%N))).
Local Notation FirstClass := (@euclidean_dimension_cast_smooth R dl dm
  (esym (addnA n (1+n)%N (1+n)%N)) (Full dl) (hFull dl)).
Local Notation Inner := (@euclidean_dimension_cast_map R ((1+n)+(1+n))%N (1+dj)%N
  (esym (addnA 1%N n (1+n)%N))).
Local Notation InnerClass := (@euclidean_dimension_cast_smooth R ((1+n)+(1+n))%N (1+dj)%N
  (esym (addnA 1%N n (1+n)%N)) (Full ((1+n)+(1+n))%N) (hFull ((1+n)+(1+n))%N)).
Local Notation Id := (fun x:R_n R n=>x).
Local Notation Second := (@euclidean_cartesian_map R n ((1+n)+(1+n))%N n (1+dj)%N Id Inner).
Local Notation SecondClass := (@current_cartesian_map_smooth R n ((1+n)+(1+n))%N n (1+dj)%N
  Id Inner (@current_join_slice_identity_smooth R n) InnerClass).

(** Source for [current_join_assoc_forward_source]: naturally
    associate ((x,a,y),b,z) into (x,a,y,b,z),
    supporting the left iterated join in Federer
    4.1.11, p. 366. These are the preceding maps. *)
Definition current_join_assoc_forward_source (p:R_n R dl):R_n R df:=Second (First p).

(** Source for [current_join_assoc_forward_source_coordinates]: both
    associations retain every original ordered coordinate,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_forward_source_coordinates (x y z:R_n R n) (a b:R_n R 1%N):
  current_join_assoc_forward_source (@euclidean_block_join R dj (1+n)%N
    (@euclidean_block_join R n (1+n)%N (x,@euclidean_block_join R 1%N n (a,y)),
      @euclidean_block_join R 1%N n (b,z)))=
  @euclidean_block_join R n (1+dj)%N
    (x,@euclidean_block_join R 1%N dj (a,@euclidean_block_join R n (1+n)%N
      (y,@euclidean_block_join R 1%N n (b,z)))).
Proof.
rewrite /current_join_assoc_forward_source euclidean_cartesian_reassociate_join
  /euclidean_cartesian_map euclidean_block_joinK.
cbn beta iota.
by rewrite euclidean_cartesian_reassociate_join.
Qed.

(** Source for [current_join_assoc_left_source_point_cover]: every
    original left source has its original five ordered
    coordinates, supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_source_point_cover (p:R_n R dl):
  exists (x y z:R_n R n) (a b:R_n R 1%N),
    @euclidean_block_join R dj (1+n)%N
      (@euclidean_block_join R n (1+n)%N (x,@euclidean_block_join R 1%N n (a,y)),
        @euclidean_block_join R 1%N n (b,z))=p.
Proof.
pose q:=@euclidean_block_split R dj (1+n)%N p.
pose r:=@euclidean_block_split R n (1+n)%N q.1.
pose s:=@euclidean_block_split R 1%N n r.2.
pose t:=@euclidean_block_split R 1%N n q.2.
exists r.1;exists s.2;exists t.2;exists s.1;exists t.1.
by rewrite /s euclidean_block_splitK /r euclidean_block_splitK /t euclidean_block_splitK /q euclidean_block_splitK.
Qed.

(** Source for [current_join_assoc_forward_source_inverse]: the
    original reverse grouping is a left inverse of the
    forward source association, supporting Federer 4.1.11,
    p. 366. This is an exact pointwise coordinate law. *)
Lemma current_join_assoc_forward_source_inverse:
  cancel current_join_assoc_forward_source (@current_join_assoc_left_regroup R n).
Proof.
move=>p;have[x [y [z [a [b hPoint]]]]]:=current_join_assoc_left_source_point_cover p.
by rewrite -hPoint current_join_assoc_forward_source_coordinates current_join_assoc_left_regroup_coordinates.
Qed.

(** Source for [current_join_assoc_forward_source_smooth]: both
    original forward associations are smooth, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_forward_source_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R dl))
    (inner_norm_real_norm (@euclidean_inner_productP R df)) (Full dl) current_join_assoc_forward_source.
Proof.
exact:(@current_smooth_composite_class R dl dm df (Full dl) (Full dm)
  First Second (fun _ _=>Logic.I) FirstClass SecondClass).
Qed.

(** Source for [current_join_assoc_left_regroup_smooth]: the
    original reverse source identification is smooth,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_regroup_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R df))
    (inner_norm_real_norm (@euclidean_inner_productP R dl)) (Full df)
    (@current_join_assoc_left_regroup R n).
Proof.
exact:(@euclidean_dimension_cast_smooth R df dl (current_join_assoc_left_dimension n)
  (Full df) (hFull df)).
Qed.
End CurrentJoinAssociativityLeftSourceMaps.
