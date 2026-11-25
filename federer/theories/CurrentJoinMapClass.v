(** Federer (1969), 4.1.11, pp. 364–365: the original map
    F(x,t,y)=(1-t)x+ty is smooth. Reuse bounded linear coordinates
    and the scalar-product calculus of 3.1.11. The argument uses only
    the opaque map's public formula and works in every dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormRegularity NormRegularityOperations NormRegularityBilinear
  NormFiniteLinearBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanScalarCoordinateMaps CurrentJoinMapUP CurrentJoinMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentJoinMapClass.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ :=
  (inner_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ :=
  (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation first := (@euclidean_first_block_map R n (1+n)%N).
Local Notation rest := (@euclidean_last_block_map R n (1+n)%N).
Local Notation middle :=
  (hom_comp (@euclidean_first_block_map R 1%N n) rest).
Local Notation last :=
  (hom_comp (@euclidean_last_block_map R 1%N n) rest).
Local Notation time :=
  (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) middle).
Local Notation F := (@CurrentJoinMap.value R n).

(** Source for [current_join_map_coordinates]: the original
    affine formula at every point of the ordered x,t,y product,
    supporting Federer 4.1.11, p. 364. No implementation is unfolded. *)
Lemma current_join_map_coordinates z :
  F z = (1-time z) *: first z + time z *: last z.
Proof.
have hRest : @euclidean_block_join R 1%N n
    (@euclidean_one_embed R (time z),last z) = rest z.
  change (@euclidean_block_join R 1%N n
    (@euclidean_one_embed R
      (@euclidean_one_project R (@euclidean_first_block_map R 1%N n
        (rest z))),@euclidean_last_block_map R 1%N n (rest z))=rest z).
  by rewrite euclidean_one_projectK; exact: euclidean_block_splitK.
have hPoint : @euclidean_block_join R n (1+n)%N
    (first z,@euclidean_block_join R 1%N n
      (@euclidean_one_embed R (time z),last z))=z.
  by rewrite hRest; exact: euclidean_block_splitK.
by rewrite -{1}hPoint CurrentJoinMap.laws.
Qed.

Variable W : set Z.
Hypothesis hW : forall z, W z -> norm_domain_interior NZ W z.

(** Source for [current_join_map_smooth]: the original join
    pushforward uses the smooth map F, Federer 4.1.11, p. 364.
    Only openness of its original domain is used; properness will
    follow separately from the compact current support. *)
Theorem current_join_map_smooth :
  norm_class_all_orders hNZ hNX W F.
Proof.
have hTime : norm_bounded_linear NZ (fun t : R^o => `|t|) time.
  exact: (@norm_finite_linear_bounded R Z R^o NZ (fun t : R^o => `|t|)
    hNZ hAbs (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
    (@coordinate_basisP R (n+(1+n))%N) time).
have hFirst : norm_bounded_linear NZ NX first.
  exact: (@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
    (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
    (@coordinate_basisP R (n+(1+n))%N) first).
have hLast : norm_bounded_linear NZ NX last.
  exact: (@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
    (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
    (@coordinate_basisP R (n+(1+n))%N) last).
move=> k.
have ht := @norm_class_linear R Z R^o NZ (fun t : R^o => `|t|)
  hNZ hAbs W time k hW hTime.
have hx := @norm_class_linear R Z X NZ NX hNZ hNX
  W first k hW hFirst.
have hy := @norm_class_linear R Z X NZ NX hNZ hNX
  W last k hW hLast.
have hOne := @norm_class_constant R Z R^o NZ (fun t : R^o => `|t|)
  hNZ hAbs W 1 k hW.
have hLeft := norm_class_scalar_product (norm_class_subtract hOne ht) hx.
have hRight := norm_class_scalar_product ht hy.
apply: (norm_class_domain_agreement _ (norm_class_add hLeft hRight)).
by move=> z _; rewrite current_join_map_coordinates.
Qed.
End CurrentJoinMapClass.
