(** Federer (1969), 4.1.11, p. 366: smoothness
    of the original H. Reuse bounded finite-dimensional
    linear coordinates and the scalar-product calculus;
    do not unfold the sealed existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormFiniteLinearBound
  NormRegularity NormRegularityOperations NormRegularityBilinear InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockLinearMaps
  EuclideanScalarCoordinateMaps CurrentJoinAssociatorMapsSealed CurrentJoinAssociatorMapsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinBarycentreClass.
Variable R:realType.
Variable n:nat.
Local Notation d := ((n+(n+(n+3)))%N).
Local Notation X := (R_n R d).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R d)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R d)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation first := (@euclidean_first_block_map R n (n+(n+3))%N).
Local Notation rest := (@euclidean_last_block_map R n (n+(n+3))%N).
Local Notation second := (hom_comp (@euclidean_first_block_map R n (n+3)%N) rest).
Local Notation thirdrest := (hom_comp (@euclidean_last_block_map R n (n+3)%N) rest).
Local Notation third := (hom_comp (@euclidean_first_block_map R n 3%N) thirdrest).
Local Notation weights := (hom_comp (@euclidean_last_block_map R n 3%N) thirdrest).

(** Source for [current_join_barycentre_smooth]: the original
    H is smooth on the full ordered four-factor
    Euclidean domain, supporting the associativity proof
    in Federer 4.1.11, p. 366. All dimensions,
    including zero, are retained. *)
Lemma current_join_barycentre_smooth:
  norm_class_all_orders hNX hNY Full (@CurrentJoinAssociatorMaps.barycentre R n).
Proof.
move=>k.
have hVector (L:Hom X Y):norm_class hNX hNY Full L k.
  apply:(@norm_class_linear R X Y NX NY hNX hNY Full L k hFull).
  exact:(@norm_finite_linear_bounded R X Y NX NY hNX hNY d
    (@coordinate_basis R d) (@coordinate_basisP R d) L).
have hScalar (L:Hom X R^o):norm_class hNX hAbs Full L k.
  apply:(@norm_class_linear R X R^o NX (fun r:R^o=>`|r|) hNX hAbs Full L k hFull).
  exact:(@norm_finite_linear_bounded R X R^o NX (fun r:R^o=>`|r|) hNX hAbs d
    (@coordinate_basis R d) (@coordinate_basisP R d) L).
have hWeight i:=hScalar (hom_comp (@euclidean_scalar_coordinate_map R 3%N i) weights).
have hFirst:=norm_class_scalar_product (hWeight ord0) (hVector first).
have hSecond:=norm_class_scalar_product (hWeight (lift ord0 ord0)) (hVector second).
have hThird:=norm_class_scalar_product (hWeight (lift ord0 (lift ord0 ord0))) (hVector third).
apply:(norm_class_domain_agreement _ (norm_class_add (norm_class_add hFirst hSecond) hThird)).
move=>x _;by rewrite current_join_barycentre_coordinates.
Qed.
End CurrentJoinBarycentreClass.
