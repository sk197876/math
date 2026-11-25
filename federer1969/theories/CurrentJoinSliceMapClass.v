(** Federer (1969), 4.1.11, p. 365: the original
    insertion G_t is smooth and F composed with G_t is
    (1-t)x+ty. Reuse the public coordinate laws, existing
    componentwise map and already proved linear calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentCartesianPointInclusion
  CurrentCartesianMapClass CurrentCartesianDomain CurrentJoinDomain
  CurrentJoinMapUP CurrentJoinMapSealed
  CurrentJoinSliceMapUP CurrentJoinSliceMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentJoinSliceMapClass.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Source := (R_n R (n+n)%N).
Local Notation Target := (R_n R (n+(1+n))%N).
Local Notation Full := (fun _ : X => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hSource :=
  (inner_norm_real_norm (@euclidean_inner_productP R (n+n)%N)).
Local Notation hTarget :=
  (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation p := (@euclidean_first_block_map R n n).
Local Notation q := (@euclidean_last_block_map R n n).
Variable t : R.
Local Notation G := (@CurrentJoinSliceMap.value R n t).
Local Notation point := (fun (x y : X) =>
  @euclidean_block_join R n (1+n)%N
    (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).
Local Notation insert :=
  (@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t)).

(** Source for [current_join_slice_map_coordinates]: the
    original coordinates of G_t at every product point, supporting
    Federer 4.1.11, p. 365. Use the opaque public formula only. *)
Lemma current_join_slice_map_coordinates z : G z = point (p z) (q z).
Proof.
have hz : @euclidean_block_join R n n (p z,q z)=z.
  exact: euclidean_block_splitK.
by rewrite -{1}hz CurrentJoinSliceMap.laws.
Qed.

(** Source for [current_join_slice_map_as_product]: G_t is
    the identity times the preceding point inclusion, supporting
    the original product identity in Federer 4.1.11, p. 365. *)
Theorem current_join_slice_map_as_product :
  G = @euclidean_cartesian_map R n n n (1+n)%N
    (fun x : X => x) insert.
Proof.
apply: funext => z.
apply: (can_inj (@euclidean_block_splitK R n (1+n)%N)).
by rewrite current_join_slice_map_coordinates euclidean_block_joinK.
Qed.

(** Source for [current_join_slice_identity_smooth]: the
    identity factor is smooth by the earlier linear class theorem,
    supporting G_t in Federer 4.1.11, p. 365. *)
Theorem current_join_slice_identity_smooth :
  norm_class_all_orders hNX hNX Full (fun x : X => x).
Proof.
pose Id := hom_of_linear (@linear_id R X).
have hId : norm_bounded_linear NX NX Id.
  exists 1; split; first exact: ler01.
  by move=> x; rewrite /Id hom_of_linearE /= mul1r.
move=> k.
exact: (@norm_class_linear R X X NX NX hNX hNX Full Id k hFull hId).
Qed.

(** Source for [current_join_slice_map_smooth]: the original
    insertion G_t is smooth on its Euclidean source, supporting
    the pushforward identity of Federer 4.1.11, p. 365. *)
Theorem current_join_slice_map_smooth :
  norm_class_all_orders hSource hTarget (fun _ => True) G.
Proof.
rewrite current_join_slice_map_as_product.
exact: (@current_cartesian_map_smooth R n n n (1+n)%N
  (fun x : X => x) insert current_join_slice_identity_smooth
  (@current_cartesian_point_inclusion_smooth R 1%N n Full hFull
    (@euclidean_one_embed R t))).
Qed.

(** Source for [current_join_slice_map_domain_image]: the
    original G_t maps the x,y product into the x,t,y domain,
    supporting Federer 4.1.11, p. 365. All factors here are
    the original full Euclidean spaces. *)
Definition current_join_slice_map_domain_image :
  forall z, @euclidean_cartesian_set R n n Full Full z ->
    @current_join_domain R n (G z) :=
  fun _ _ => conj Logic.I (conj Logic.I Logic.I).

(** Source for [current_join_slice_map_open_smooth]: the
    original insertion is smooth on the actual Cartesian source,
    supporting the pushforward in Federer 4.1.11, p. 365.
    This is the preceding open restriction of its global class. *)
Theorem current_join_slice_map_open_smooth :
  norm_class_all_orders hSource hTarget
    (@euclidean_cartesian_set R n n Full Full) G.
Proof.
move=> k.
exact: (@norm_class_open_restriction R Source Target
  (inner_norm (@euclidean_inner_productP R (n+n)%N))
  (inner_norm (@euclidean_inner_productP R (n+(1+n))%N))
  hSource hTarget (fun _ => True)
  (@euclidean_cartesian_set R n n Full Full) G k
  (fun _ _ => Logic.I)
  (@current_cartesian_domain_open R n n Full Full hFull hFull)
  (current_join_slice_map_smooth k)).
Qed.

(** Source for [current_join_map_after_slice]: the original
    F(G_t(x,y))=(1-t)x+ty, supporting the endpoint projection
    identities of Federer 4.1.11, p. 365. *)
Theorem current_join_map_after_slice z :
  @CurrentJoinMap.value R n (G z) = (1-t)*:p z+t*:q z.
Proof.
by rewrite current_join_slice_map_coordinates CurrentJoinMap.laws.
Qed.
End CurrentJoinSliceMapClass.

(** Source for [current_join_start_projection]: F composed
    with G_0 is the first original standard projection,
    Federer 4.1.11, p. 365, opening paragraph. *)
Lemma current_join_start_projection (R : realType) n
    (z : R_n R (n+n)%N) :
  @CurrentJoinMap.value R n (@CurrentJoinSliceMap.value R n 0 z) =
    @euclidean_first_block_map R n n z.
Proof.
by rewrite current_join_map_after_slice subr0 scale1r scale0r addr0.
Qed.

(** Source for [current_join_end_projection]: F composed
    with G_1 is the second original standard projection,
    Federer 4.1.11, p. 365, opening paragraph. *)
Lemma current_join_end_projection (R : realType) n
    (z : R_n R (n+n)%N) :
  @CurrentJoinMap.value R n (@CurrentJoinSliceMap.value R n 1 z) =
    @euclidean_last_block_map R n n z.
Proof.
by rewrite current_join_map_after_slice subrr scale0r scale1r add0r.
Qed.
