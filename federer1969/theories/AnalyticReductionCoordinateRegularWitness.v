(** Federer (1969), 3.4.8(8), p. 329:
    original B_j membership supplies a regular
    germ on the original j-dimensional prefix.
    Reuse exact prefix membership, directional
    pullback, proper-ideal vanishing and least order. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermRing
  AnalyticGermJetsSealed AnalyticGermValueSealed AnalyticGermValueZerothJet
  AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws CommutativeIdealUP
  AnalyticRotatedGermIdeal AnalyticReductionLociUP AnalyticReductionActual
  AnalyticPrefixCoordinatesSealed AnalyticPrefixBasisValues AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  AnalyticPrefixGermSubring AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  PointedAnalyticPullbackValue PointedAnalyticLinearPullbackDiagonal
  AnalyticDirectionalRegularOrder WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_coordinate_regular_witness]:
    the original r(j) and regular prefix
    germ used for preparation in 3.4.8(8),
    p. 329. Every hypothesis comes from
    the original proper ideal and B_j;
    the regularity conclusion is proved along
    the prescribed last prefix coordinate. *)
Theorem analytic_reduction_coordinate_regular_witness (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (j:'I_n) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  exists beta:@analytic_germ_ring R (R_n R (j:nat).+1)
      (inner_norm (@euclidean_inner_productP R (j:nat).+1))
      (inner_norm_real_norm (@euclidean_inner_productP R (j:nat).+1)) 0,
    @analytic_rotated_germ_ideal R X B hB n e he I g
      (@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega
        (j:nat).+1 (ltn_ord j) beta) /\
    exists k,is_weierstrass_regular_germ beta k (@coordinate_basis R (j:nat).+1 ord_max).
Proof.
move=>hI hProper hBMember.
pose NX:=inner_norm hB.
pose hNX:=inner_norm_real_norm hB.
pose p:=(j:nat).+1.
pose Y:=R_n R p.
pose NY:=inner_norm (@euclidean_inner_productP R p).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R p).
pose projection:=@AnalyticPrefixCoordinates.projection R X n omega p (ltn_ord j).
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega p (ltn_ord j).
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have [alpha [hAlpha [hQ [k [hK hJet]]]]]:=(analytic_reduction_B_membership hLaws j g).1 hBMember.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
rewrite (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)) in hQ.
have [beta hBeta]:=(@analytic_prefix_germ_subring_membership R X NX hNX n e he omega p (ltn_ord j) alpha).1 hQ.
have hPullback:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega p (ltn_ord j).
have hProjection:=@AnalyticPrefixCoordinates.projection_laws R X n omega p (ltn_ord j).
have hIndex:widen_ord (ltn_ord j) (ord_max:'I_p) = j by apply:val_inj.
have hDirection:projection (e j) = @coordinate_basis R p ord_max.
  have hInside:=@analytic_prefix_basis_inside R X n e omega p (ltn_ord j) projection hProjection hDual (ord_max:'I_p).
  have hArgument:e (widen_ord (ltn_ord j) (ord_max:'I_p)) = e j:=congr1 e hIndex.
  rewrite hArgument in hInside;exact:hInside.
have hDerivative:=@pointed_analytic_linear_pullback_diagonal R X Y NX NY hNX hNY 0 0 projection E
  hPullback (linear0 projection) k beta (e j).
rewrite hBeta hDirection in hDerivative.
have hDirectional:has_nonzero_analytic_directional_jet beta (@coordinate_basis R p ord_max).
  exists k;split;first exact:hK.
  move=>hZero;apply:hJet;by rewrite hDerivative hZero.
have hRotated:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
have hRotatedProper:=@analytic_rotated_germ_ideal_proper R X B hB n e he I g hProper.
have hValue:@AnalyticGermValue.map R X NX hNX 0 alpha = 0.
  apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0 alpha).
  exact:(@analytic_proper_ideal_vanishes R X NX hNX 0 _ hRotated hRotatedProper alpha hAlpha).
have hPullValue:=@pointed_analytic_pullback_centre_value R X Y NX NY hNX hNY 0 0 projection E hPullback
  (linear0 projection) beta.
have hBetaValue:@AnalyticGermValue.map R Y NY hNY 0 beta = 0 by rewrite -hPullValue hBeta.
have hZeroth:=(@analytic_germ_value_zeroth_jet R Y NY hNY 0 beta).1 hBetaValue.
have [r hRegular]:=@analytic_directional_regular_order_exists R Y NY hNY beta (@coordinate_basis R p ord_max)
  hZeroth hDirectional.
exists beta;split;first by rewrite hBeta.
by exists r.
Qed.
