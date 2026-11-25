(** Federer (1969), 4.1.11, p. 366: the
    original time-square maps f and g are smooth.
    Reuse the coordinate, scalar-product and addition
    calculus from 3.1.11, with their sealed formulas. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanScalarCoordinateMaps
  CurrentJoinAssociatorMapsUP CurrentJoinAssociatorMapsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinTriangleMapsClass.
Variable R:realType.
Local Notation X := (R_n R 2%N).
Local Notation Y := (R_n R 3%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 2%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 3%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 2%N)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R 3%N)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation e0 := (@coordinate_basis R 3%N ord0).
Local Notation e1 := (@coordinate_basis R 3%N (lift ord0 ord0)).
Local Notation e2 := (@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0))).

(** Source for [current_join_triangle_maps_class]: both
    original polynomial maps used for the two square
    images have every smoothness class, supporting
    Federer 4.1.11, p. 366. Their actual Euclidean
    norms and containing domains are unchanged. *)
Lemma current_join_triangle_maps_class k:
  norm_class hNX hNY Full (@CurrentJoinAssociatorMaps.left_triangle R) k /\
  norm_class hNX hNY Full (@CurrentJoinAssociatorMaps.right_triangle R) k.
Proof.
pose s:=@euclidean_scalar_coordinate_map R 2%N ord0.
pose t:=@euclidean_scalar_coordinate_map R 2%N (lift ord0 ord0).
have hs:=@norm_class_linear R X R^o NX (fun r:R^o=>`|r|) hNX hAbs Full s k hFull
  (@euclidean_scalar_coordinate_bounded R 2%N ord0).
have ht:=@norm_class_linear R X R^o NX (fun r:R^o=>`|r|) hNX hAbs Full t k hFull
  (@euclidean_scalar_coordinate_bounded R 2%N (lift ord0 ord0)).
have hOne:=@norm_class_constant R X R^o NX (fun r:R^o=>`|r|) hNX hAbs Full 1 k hFull.
have hOneMinusS:=norm_class_subtract hOne hs.
have hOneMinusT:=norm_class_subtract hOne ht.
have hLeft:=norm_class_scalar_product hOneMinusS hOneMinusT.
have hMiddle:=norm_class_scalar_product hs hOneMinusT.
have hRight:=norm_class_scalar_product hs ht.
have hConstant (v:Y):norm_class hNX hNY Full (fun _=>v) k.
  exact:(@norm_class_constant R X Y NX NY hNX hNY Full v k hFull).
have hLeftTerm:=norm_class_scalar_product hLeft (hConstant e0).
have hMiddleTerm:=norm_class_scalar_product hMiddle (hConstant e1).
have hLastTerm:=norm_class_scalar_product ht (hConstant e2).
have hRightFirstTerm:=norm_class_scalar_product hOneMinusS (hConstant e0).
have hRightLastTerm:=norm_class_scalar_product hRight (hConstant e2).
split.
- apply:(norm_class_domain_agreement _ (norm_class_add (norm_class_add hLeftTerm hMiddleTerm) hLastTerm)).
  move=>u _;by rewrite CurrentJoinAssociatorMaps.left_triangle_laws.
- apply:(norm_class_domain_agreement _ (norm_class_add (norm_class_add hRightFirstTerm hMiddleTerm) hRightLastTerm)).
  move=>u _;by rewrite CurrentJoinAssociatorMaps.right_triangle_laws.
Qed.

(** Source for [current_join_left_triangle_smooth]: the
    original f is smooth, supporting its proper square
    pushforward in Federer 4.1.11, p. 366. *)
Lemma current_join_left_triangle_smooth:
  norm_class_all_orders hNX hNY Full (@CurrentJoinAssociatorMaps.left_triangle R).
Proof. move=>k;exact:(current_join_triangle_maps_class k).1. Qed.

(** Source for [current_join_right_triangle_smooth]: the
    original g is smooth, supporting its proper square
    pushforward in Federer 4.1.11, p. 366. *)
Lemma current_join_right_triangle_smooth:
  norm_class_all_orders hNX hNY Full (@CurrentJoinAssociatorMaps.right_triangle R).
Proof. move=>k;exact:(current_join_triangle_maps_class k).2. Qed.
End CurrentJoinTriangleMapsClass.
