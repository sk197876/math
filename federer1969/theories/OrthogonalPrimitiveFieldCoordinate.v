(** Federer (1969), 3.4.8(8), p. 330:
    the original primitive real combination
    in L is exactly the image of
    the original inverse-rotated coordinate germ.
    Apply the checked germ identity and
    original coefficient scalar triangles. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermRing AnalyticCoordinateGermsSealed AnalyticScalarsSealed
  AnalyticPrefixGermMap AnalyticPrefixRealScalars AnalyticOrthogonalPullback OrthogonalCoordinateFixing
  OrdinalCoordinateTail OrthogonalPrimitiveCoordinateGerm CoefficientFractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OriginalCoordinate.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Hypothesis hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o (pi \o E)) _) eta phi.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation realPrefix:=(@AnalyticScalars.map R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0).
Local Notation realAmbient:=(@AnalyticScalars.map R X NX hNX 0).
Variables q h:@orthogonal_group R X B hB n e he.

(** Source for [orthogonal_primitive_field_coordinate]: the
    actual field equality used before clearing
    denominators in 3.4.8(8), p. 330.
    It identifies the exact original primitive
    element; no equality of selected quotient
    or coefficient implementations is assumed. *)
Theorem orthogonal_primitive_field_coordinate:
  (forall x:X,orthogonal_element_map q (orthogonal_element_map h x) = x) ->
  @analytic_suffix_rotation_group R X B hB n e he m q ->
  inclusion (pi (@analytic_orthogonal_germ_map R X B hB n e he h (gamma m))) =
  \sum_(i<n-m) phi (eta (realPrefix
    (omega (ordinal_coordinate_tail_index hMN i) (orthogonal_element_map q (e m)))))*
    inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))).
Proof.
move=>hInverse hQ.
have hScalar c:phi (eta (realPrefix c)) = inclusion (pi (realAmbient c)).
  rewrite (coefficient_fraction_scalar_triangle hCoefficient).
  change (inclusion (pi (E (realPrefix c))) = inclusion (pi (realAmbient c))).
  by rewrite analytic_prefix_real_scalar_triangle.
have hGerm:=@orthogonal_primitive_coordinate_germ R X B hB n e he hON omega hDual q h m hMN hInverse hQ.
rewrite hGerm !rmorph_sum.
apply:eq_bigr=>i _;by rewrite !rmorphM hScalar.
Qed.
End OriginalCoordinate.
