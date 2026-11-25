(** Federer (1969), 4.1.11, p. 365: the exact
    exterior differential image of the original x,t,y
    multivector. The three differential directions and
    the exterior functor laws retain the printed sharp weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts ExteriorNormNaturality
  ExteriorMapScaling ExteriorDegreeOneNorm CurrentMapDifferential CurrentCartesianVectorProduct
  CurrentJoinMapSealed CurrentJoinMapDifferential CurrentJoinBlockDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinExteriorDifferential.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R (1+n)%N).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation P := (@euclidean_first_injection_map R n (1+n)%N).
Local Notation Q := (@euclidean_last_injection_map R n (1+n)%N).
Local Notation PTime := (@euclidean_first_injection_map R 1%N n).
Local Notation QSpace := (@euclidean_last_injection_map R 1%N n).
Local Notation first := (@euclidean_first_block_map R n (1+n)%N).
Local Notation rest := (@euclidean_last_block_map R n (1+n)%N).
Local Notation middle := (hom_comp (@euclidean_first_block_map R 1%N n) rest).
Local Notation last := (hom_comp (@euclidean_last_block_map R 1%N n) rest).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) middle).
Local Notation Point a s b := (@euclidean_block_join R n (1+n)%N
  (a,@euclidean_block_join R 1%N n (@euclidean_one_embed R s,b))).
Variable U:set Z.
Hypothesis hU:forall z,U z->norm_domain_interior NZ U z.
Variable z:Z.
Hypothesis hz:U z.
Local Notation DF := (@current_map_differential R (n+(1+n))%N n U (@CurrentJoinMap.value R n) z).

(** Source for [current_join_first_exterior_differential]:
    the first spatial i-vector is multiplied by (1-t)^i,
    supporting the first mass display in Federer 4.1.11,
    p. 365, by the exterior functor laws of 1.3.1, p. 14. *)
Lemma current_join_first_exterior_differential i (a:exterior_power X i):
  exterior_power_map (hom_as_linear DF) i (exterior_power_map (hom_as_linear P) i a)=
    (1-time z)^+i*:a.
Proof.
have hZero:@euclidean_block_join R 1%N n (@euclidean_one_embed R 0,(0:X))=0.
  have hEmbed:@euclidean_one_embed R 0=0 by apply/ffunP=>k;rewrite /euclidean_one_embed !ffunE.
  rewrite hEmbed;exact:(lin0 (@euclidean_block_join_linear R 1%N n)).
have hPoint x:P x=Point x 0 0.
  change (@euclidean_block_join R n (1+n)%N (x,0)=Point x 0 0).
  by rewrite hZero.
have hLinear x:(linear_comp (hom_as_linear DF) (hom_as_linear P)) x=(1-time z)*:x.
  change (DF (P x)=(1-time z)*:x).
  rewrite hPoint (@current_join_map_block_differential R n U hU z hz x 0 0)
    scale0r scaler0 !addr0;by [].
rewrite exterior_power_map_composition.
have hScale:=@exterior_power_map_scale R X X (linear_id X)
  (linear_comp (hom_as_linear DF) (hom_as_linear P)) (1-time z) hLinear i a.
by rewrite exterior_power_map_identity in hScale.
Qed.

(** Source for [current_join_last_exterior_differential]:
    the last spatial j-vector is multiplied by t^j,
    supporting the original sharp mass weight in Federer
    4.1.11, p. 365. No positivity of t is needed here. *)
Lemma current_join_last_exterior_differential j (b:exterior_power X j):
  exterior_power_map (hom_as_linear DF) j
    (exterior_power_map (hom_as_linear Q) j
      (exterior_power_map (hom_as_linear QSpace) j b))=time z^+j*:b.
Proof.
have hZero:@euclidean_one_embed R 0=0 by apply/ffunP=>k;rewrite /euclidean_one_embed !ffunE.
have hPoint x:Q (QSpace x)=Point 0 0 x.
  change (@euclidean_block_join R n (1+n)%N
    (0,@euclidean_block_join R 1%N n (0,x))=Point 0 0 x).
  by rewrite hZero.
have hLinear x:(linear_comp (hom_as_linear DF)
    (linear_comp (hom_as_linear Q) (hom_as_linear QSpace))) x=time z*:x.
  change (DF (Q (QSpace x))=time z*:x).
  rewrite hPoint (@current_join_map_block_differential R n U hU z hz 0 0 x)
    scaler0 scale0r !add0r;by [].
rewrite (@exterior_power_map_composition R X W Z (hom_as_linear QSpace) (hom_as_linear Q))
  exterior_power_map_composition.
have hScale:=@exterior_power_map_scale R X X (linear_id X)
  (linear_comp (hom_as_linear DF) (linear_comp (hom_as_linear Q) (hom_as_linear QSpace)))
  (time z) hLinear j b.
by rewrite exterior_power_map_identity in hScale.
Qed.

(** Source for [current_join_time_exterior_differential]:
    the original positive time vector has image y-x,
    supporting Federer 4.1.11, p. 365, first mass display. *)
Lemma current_join_time_exterior_differential:
  exterior_power_map (hom_as_linear DF) 1%N
    (exterior_power_map (hom_as_linear Q) 1%N
      (exterior_power_map (hom_as_linear PTime) 1%N
        (exterior_first_inclusion (R_n R 1%N) (@euclidean_one_embed R 1))))=
    exterior_first_inclusion X (last z-first z).
Proof.
rewrite !exterior_map_first_inclusion.
congr (exterior_first_inclusion _ _).
change (DF (Point 0 1 0)=last z-first z).
by rewrite (@current_join_map_block_differential R n U hU z hz 0 1 0)
  !scaler0 scale1r add0r addr0.
Qed.

(** Source for [current_join_exterior_differential]: the
    actual three-factor coefficient is sent to
    (1-t)^i xi wedge (y-x) wedge t^j eta, exactly as in
    Federer 4.1.11, p. 365, first mass display. The
    ordered association has degree i+(1+j). *)
Theorem current_join_exterior_differential i j
    (a:exterior_power X i) (b:exterior_power X j):
  exterior_power_map (hom_as_linear DF) (i+(1+j))%N
    (@current_cartesian_vector_product R n (1+n)%N i (1+j)%N a
      (@current_cartesian_vector_product R 1%N n 1%N j
        (exterior_first_inclusion (R_n R 1%N) (@euclidean_one_embed R 1)) b))=
  exterior_product ((1-time z)^+i*:a)
    (exterior_product (exterior_first_inclusion X (last z-first z)) (time z^+j*:b)).
Proof.
rewrite /current_cartesian_vector_product exterior_power_map_product
  current_join_first_exterior_differential exterior_power_map_composition
  exterior_power_map_product !exterior_power_map_composition.
have hTime:=current_join_time_exterior_differential.
rewrite !exterior_power_map_composition in hTime.
have hLast:=current_join_last_exterior_differential b.
rewrite !exterior_power_map_composition in hLast.
by rewrite hTime hLast.
Qed.
End CurrentJoinExteriorDifferential.
