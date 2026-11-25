(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: an original directional B_j witness supplies
    a regular holomorphic germ on the original coordinate prefix.
    This connection retains the prescribed last coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP LinearBasis FiniteCoordinates
  HolomorphicCoordinateNorm FieldPrefixCoordinatesSealed FieldPrefixBasisValues HolomorphicPrefixGermMap
  HolomorphicPrefixGermMapLaws HolomorphicPrefixGermSubring HolomorphicCoordinateSubringFamilyUP
  HolomorphicCoordinateSubringFamilySealed HolomorphicGermUP HolomorphicGermRing HolomorphicGermValueSealed
  HolomorphicGermJetsSealed HolomorphicGermValueZerothJet HolomorphicVanishingIdealUP HolomorphicVanishingIdealSealed
  HolomorphicVanishingIdealLaws CommutativeIdealUP HolomorphicReductionLociUP PointedHolomorphicPullbackValue
  PointedHolomorphicLinearPullbackForms HolomorphicDirectionalRegularOrder ComplexWeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_prefix_regular_witness]: the original
    finite positive order used in preparation, 3.4.12, p. 339.
    Properness forces zero centre value; the first nonzero
    directional derivative and original coordinate pullback supply
    every regularity assertion. No preparation conclusion is assumed. *)
Theorem holomorphic_prefix_regular_witness (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
    (J:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)) (j:'I_n):
  is_commutative_ideal J ->~J 1 ->
  (exists alpha,J alpha /\
    @HolomorphicCoordinateSubringFamily.value R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j)) ->
  exists beta:@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) (j:nat).+1)
      (@holomorphic_coordinate_norm R (j:nat).+1) (complex_norm_real (@holomorphic_coordinate_norm_laws R (j:nat).+1)) 0,
    J (@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 (ltn_ord j) beta) /\
    exists k,is_complex_weierstrass_regular_germ (@holomorphic_coordinate_norm_laws R (j:nat).+1)
      beta k (@coordinate_basis (ComplexScalars.C R) (j:nat).+1 ord_max).
Proof.
move=>hJ hProper [alpha [hAlpha [hQ [k [hK hJet]]]]].
pose p:=(j:nat).+1.
pose Y:=coordinate_space (ComplexScalars.C R) p.
pose NY:=@holomorphic_coordinate_norm R p.
pose hNY:=@holomorphic_coordinate_norm_laws R p.
pose projection:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega p (ltn_ord j).
pose E:=@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega p (ltn_ord j).
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX (complex_norm_real hNX) n e he omega.
rewrite (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)) in hQ.
have [beta hBeta]:=(@holomorphic_prefix_germ_subring_membership R X NX (complex_norm_real hNX)
  n e he omega p (ltn_ord j) alpha).1 hQ.
have hPullback:=@holomorphic_prefix_germ_map_specification R X NX (complex_norm_real hNX) n e he omega p (ltn_ord j).
have hProjection:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega p (ltn_ord j).
have hIndex:widen_ord (ltn_ord j) (ord_max:'I_p)=j by apply:val_inj.
have hDirection:projection (e j)=@coordinate_basis (ComplexScalars.C R) p ord_max.
  have hInside:=@field_prefix_basis_inside (ComplexScalars.C R) X n e omega p (ltn_ord j)
    projection hProjection hDual (ord_max:'I_p).
  by rewrite hIndex in hInside.
have hDerivative:=@pointed_holomorphic_linear_pullback_form_diagonal R X Y NX NY hNX hNY 0 0 projection E
  hPullback (linear0 projection) k beta (e j).
rewrite hBeta hDirection in hDerivative.
have hDirectional:has_nonzero_holomorphic_directional_jet hNY beta (@coordinate_basis (ComplexScalars.C R) p ord_max).
  exists k;split;first exact:hK.
  move=>hZero;apply:hJet;by rewrite hDerivative hZero.
have hValue:@HolomorphicGermValue.map R X NX (complex_norm_real hNX) 0 alpha=0.
  apply/(@HolomorphicVanishingIdeal.laws R X NX (complex_norm_real hNX) 0 alpha).
  exact:(@holomorphic_proper_ideal_vanishes R X NX (complex_norm_real hNX) 0 J hJ hProper alpha hAlpha).
have hPullValue:=@pointed_holomorphic_pullback_centre_value R X Y NX NY (complex_norm_real hNX)
  (complex_norm_real hNY) 0 0 projection E hPullback (linear0 projection) beta.
have hBetaValue:@HolomorphicGermValue.map R Y NY (complex_norm_real hNY) 0 beta=0 by rewrite -hPullValue hBeta.
have hZeroth:=(@holomorphic_germ_value_zeroth_jet R Y NY (complex_norm_real hNY) 0 beta).1 hBetaValue.
have [r hRegular]:=@holomorphic_directional_regular_order_exists R Y NY hNY beta
  (@coordinate_basis (ComplexScalars.C R) p ord_max) hZeroth hDirectional.
exists beta;split;first by rewrite hBeta.
by exists r.
Qed.
