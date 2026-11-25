(** Federer (1969), 4.1.11, p. 365: the original affine
    identity uses A times the scalar identity times A, and
    A composed with F equals F composed with that product.
    Reuse the original affine predicate of 2.7.16, p. 133,
    and the existing Cartesian maps and smoothness laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom AffineMaps RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanAffineSmooth
  CurrentCartesianDomain CurrentCartesianMapClass CurrentCartesianMapPullback
  CurrentJoinDomain CurrentJoinMapSealed CurrentJoinSliceMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_affine_inner_map]: the original
    identity times A on the time-space factor, supporting the
    affine identity of Federer 4.1.11, p. 365. This is an alias
    of the previously defined Cartesian map. *)
Definition current_join_affine_inner_map (R:realType) m n (A:R_n R m->R_n R n):=
  @euclidean_cartesian_map R 1%N m 1%N n (fun t:R_n R 1%N=>t) A.

(** Source for [current_join_affine_map]: the original
    A times the scalar identity times A, Federer 4.1.11, p. 365,
    affine-map paragraph. Use the two preceding Cartesian maps;
    no replacement product carrier or selected map is introduced. *)
Definition current_join_affine_map (R:realType) m n (A:R_n R m->R_n R n):=
  @euclidean_cartesian_map R m (1+m)%N n (1+n)%N A
    (@current_join_affine_inner_map R m n A).

(** Source for [current_join_affine_inner_coordinates]: the
    original time coordinate is retained and A acts on the
    spatial coordinate, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_affine_inner_coordinates (R:realType) m n
    (A:R_n R m->R_n R n) t x:
  current_join_affine_inner_map A
    (@euclidean_block_join R 1%N m (@euclidean_one_embed R t,x))=
  @euclidean_block_join R 1%N n (@euclidean_one_embed R t,A x).
Proof. by rewrite /current_join_affine_inner_map /euclidean_cartesian_map euclidean_block_joinK. Qed.

(** Source for [current_join_affine_map_coordinates]: the
    original product map sends (x,t,y) to (A(x),t,A(y)),
    supporting the identity A composed with F in Federer
    4.1.11, p. 365. Empty spatial blocks are retained. *)
Lemma current_join_affine_map_coordinates (R:realType) m n
    (A:R_n R m->R_n R n) x t y:
  current_join_affine_map A
    (@euclidean_block_join R m (1+m)%N
      (x,@euclidean_block_join R 1%N m (@euclidean_one_embed R t,y)))=
  @euclidean_block_join R n (1+n)%N
    (A x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,A y)).
Proof.
by rewrite /current_join_affine_map /euclidean_cartesian_map euclidean_block_joinK
  current_join_affine_inner_coordinates.
Qed.

Section AffineMaps.
Variable R:realType.
Variables m n:nat.
Variable A:R_n R m->R_n R n.
Hypothesis hA:is_affine_map A.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation FullM := (fun _:X=>True).
Local Notation FullN := (fun _:Y=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation NM := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NN := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hFullM := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NM x).
Local Notation hFullN := (fun (y:Y) (_:True)=>@norm_full_domain_interior R Y NN y).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeM := (@euclidean_cartesian_set R 1%N m Time FullM).
Local Notation TimeN := (@euclidean_cartesian_set R 1%N n Time FullN).
Local Notation hTimeM := (@current_cartesian_domain_open R 1%N m Time FullM hTime hFullM).
Local Notation Inner := (@current_join_affine_inner_map R m n A).
Local Notation Product := (@current_join_affine_map R m n A).
Local Notation AGlobal := (@euclidean_affine_map_smooth R m n FullM hFullM A hA).
Local Notation IdTime := (fun t:R_n R 1%N=>t).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R 1%N).
Local Notation AImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation IdImage := (fun (t:R_n R 1%N) (_:True)=>Logic.I).

(** Source for [current_join_affine_inner_image]: the
    original identity times A maps the time-space source to
    its time-space target, supporting Federer 4.1.11, p. 365. *)
Definition current_join_affine_inner_image:forall z,TimeM z->TimeN (Inner z):=
  fun z hz=>@current_cartesian_map_domain_image R 1%N m 1%N n
    Time FullM Time FullN IdTime A IdImage AImage z hz.

(** Source for [current_join_affine_map_image]: A times
    identity times A preserves the original ordered domains,
    supporting the affine identity in Federer 4.1.11, p. 365. *)
Definition current_join_affine_map_image:
  forall z,@current_join_domain R m z->@current_join_domain R n (Product z):=
  fun z hz=>@current_cartesian_map_domain_image R m (1+m)%N n (1+n)%N
    FullM TimeM FullN TimeN A Inner AImage current_join_affine_inner_image z hz.

(** Source for [current_join_affine_inner_smooth]: identity
    times A is globally smooth by the preceding affine and
    Cartesian calculus, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_affine_inner_smooth:
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R (1+m)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)) (fun _=>True) Inner.
Proof. exact:(@current_cartesian_map_smooth R 1%N m 1%N n IdTime A IdGlobal AGlobal). Qed.

(** Source for [current_join_affine_map_smooth]: the original
    A times identity times A is globally smooth, supporting
    the affine join identity of Federer 4.1.11, p. 365. *)
Theorem current_join_affine_map_smooth:
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R (m+(1+m))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)) (fun _=>True) Product.
Proof.
exact:(@current_cartesian_map_smooth R m (1+m)%N n (1+n)%N
  A Inner AGlobal current_join_affine_inner_smooth).
Qed.

(** Source for [current_join_affine_map_open_smooth]: the
    same product map is smooth on the original ordered source,
    supporting its actual pushforward in Federer 4.1.11, p. 365.
    This alias uses the preceding open-product restriction. *)
Definition current_join_affine_map_open_smooth:
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R (m+(1+m))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N))
    (@current_join_domain R m) Product:=
  @current_cartesian_map_on_open_product_smooth R m (1+m)%N n (1+n)%N
    A Inner AGlobal current_join_affine_inner_smooth FullM TimeM hFullM hTimeM.

(** Source for [current_join_affine_map_commutes]: F composed
    with A times identity times A equals A composed with F,
    the original reason for affine naturality in Federer 4.1.11,
    p. 365. The affine law applies at every real time. *)
Theorem current_join_affine_map_commutes z:
  @CurrentJoinMap.value R n (Product z)=A (@CurrentJoinMap.value R m z).
Proof.
pose a:=@euclidean_block_split R m (1+m)%N z.
pose b:=@euclidean_block_split R 1%N m a.2.
have hz:@euclidean_block_join R m (1+m)%N
    (a.1,@euclidean_block_join R 1%N m (@euclidean_one_embed R (@euclidean_one_project R b.1),b.2))=z.
  by rewrite euclidean_one_projectK /b euclidean_block_splitK /a euclidean_block_splitK.
rewrite -hz current_join_affine_map_coordinates !CurrentJoinMap.laws.
exact:esym (@euclidean_affine_segment_values R m n A hA a.1 b.2 (@euclidean_one_project R b.1)).
Qed.
End AffineMaps.
