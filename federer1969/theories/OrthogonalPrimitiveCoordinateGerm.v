(** Federer (1969), 3.4.8(8), p. 330:
    the original primitive coordinate combination
    is exactly the germ of omega_m q^-1.
    Apply the original inverse-coordinate identity
    and the existing finite-sum representative theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies NormFiniteLinearBound OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives PointedFunctionalGermExistence
  AnalyticCoordinateGermsSealed AnalyticScalarsSealed AnalyticOrthogonalPullback
  OrthogonalCoordinateFixing OrdinalCoordinateTail OrthogonalSuffixCovector AnalyticCoordinateLinearCombination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_primitive_coordinate_germ]:
    the exact original equality of the
    primitive real coordinate sum and the
    inverse-rotated coordinate germ, 3.4.8(8),
    p. 330. Every coefficient is the
    corresponding original omega_j(q(e_m)). All
    representative witnesses remain local. *)
Theorem orthogonal_primitive_coordinate_germ (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  (q h:@orthogonal_group R X B hB n e he) (m:'I_n) (hMN:((m:nat)<=n)%N):
  (forall x:X,orthogonal_element_map q (orthogonal_element_map h x) = x) ->
  @analytic_suffix_rotation_group R X B hB n e he m q ->
  @analytic_orthogonal_germ_map R X B hB n e he h
    (@AnalyticCoordinateGerms.value R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega m) =
  \sum_(i<n-m) (@AnalyticScalars.map R X (inner_norm hB) (inner_norm_real_norm hB) 0
    (omega (ordinal_coordinate_tail_index hMN i) (orthogonal_element_map q (e m))))*
    (@AnalyticCoordinateGerms.value R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega
      (ordinal_coordinate_tail_index hMN i)).
Proof.
move=>hInverse hQ.
pose NX:=inner_norm hB.
pose hNX:=inner_norm_real_norm hB.
have hBound:=@norm_finite_linear_bounded R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) n e he (omega m).
have [f hF]:=@pointed_functional_representative_exists R X NX hNX 0 (omega m) hBound.
have hValues x:analytic_representative_value f x = omega m x by rewrite hF subr0.
have hGamma:=@AnalyticCoordinateGerms.laws R X NX hNX n e he omega m f hValues.
have [g [hG hPullValues]]:=(@analytic_orthogonal_germ_map_specification R X B hB n e he h) f.
rewrite hGamma in hG;rewrite hG.
apply:(@analytic_coordinate_linear_combination_germ R X NX hNX n e he omega
  [the finType of 'I_(n-m)] (ordinal_coordinate_tail_index hMN)
  (fun i=>omega (ordinal_coordinate_tail_index hMN i) (orthogonal_element_map q (e m))) g)=>x.
rewrite hPullValues hValues.
exact:(@orthogonal_primitive_suffix_covector R X B hB n e he hON omega hDual q h hInverse m hMN hQ x).
Qed.
