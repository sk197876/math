(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: an original A_j witness has a positive first nonzero
    jet in the actual complex prefix ring. Reuse proper-ideal
    vanishing, exact pullback values and Taylor injectivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import FiniteCoordinates FieldPrefixCoordinatesSealed HolomorphicCoordinateNorm
  HolomorphicGermRingLaws HolomorphicGermJetsSealed HolomorphicGermFirstNonzeroJet HolomorphicGermValueSealed
  HolomorphicGermValueZerothJet HolomorphicVanishingIdealSealed HolomorphicVanishingIdealLaws CommutativeIdealUP
  HolomorphicRotatedGermIdeal HolomorphicReductionLociUP HolomorphicReductionActual HolomorphicPrefixGermMap
  HolomorphicPrefixGermMapLaws HolomorphicPrefixGermSubring HolomorphicCoordinateSubringFamilyUP
  HolomorphicCoordinateSubringFamilySealed PointedHolomorphicPullbackValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Witness.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable I:set G.
Variable j:'I_n.+1.
Variable g:U.
(** Source for [holomorphic_reduction_prefix_witness]: original
    A_j membership supplies the actual prefix germ and its positive
    first nonzero derivative order, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_prefix_witness:
  is_commutative_ideal I ->~I 1 ->
  @holomorphic_reduction_actual_A R X H hH n e he omega I j g ->
  exists beta:@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) j)
    (@holomorphic_coordinate_norm R j) (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) 0,
    @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g
      (@holomorphic_prefix_germ_map R X NX hNXR n e he omega j (ltn_ord j) beta) /\
    beta<>0 /\exists k,(0<k)%N /\
      @HolomorphicGermJets.value R (coordinate_space (ComplexScalars.C R) j) (@holomorphic_coordinate_norm R j)
        (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) 0 k beta<>0 /\
      forall i,(i<k)%N ->@HolomorphicGermJets.value R (coordinate_space (ComplexScalars.C R) j)
        (@holomorphic_coordinate_norm R j) (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) 0 i beta=0.
Proof.
move=>hI hProper hA.
pose Y:=coordinate_space (ComplexScalars.C R) j.
pose NY:=@holomorphic_coordinate_norm R j.
pose hNY:=complex_norm_real (@holomorphic_coordinate_norm_laws R j).
pose P:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega j (ltn_ord j).
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have [_ [alpha [hAlpha [hQ hNonzero]]]]:=(holomorphic_reduction_A_membership hLaws j g).1 hA.
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
rewrite (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)) in hQ.
have [beta hBeta]:=(@holomorphic_prefix_germ_subring_membership R X NX hNXR n e he omega j (ltn_ord j) alpha).1 hQ.
have hBetaNonzero:beta<>0.
  move=>hZero;apply:hNonzero;by rewrite -hBeta hZero rmorph0.
have hRotated:=@holomorphic_rotated_germ_ideal_is_ideal R X H hH (n+n) eR heR I g hI.
have hRotatedProper:=@holomorphic_rotated_germ_ideal_proper R X H hH (n+n) eR heR I g hProper.
have hValue:@HolomorphicGermValue.map R X NX hNXR 0 alpha = 0.
  apply/(@HolomorphicVanishingIdeal.laws R X NX hNXR 0 alpha).
  exact:(@holomorphic_proper_ideal_vanishes R X NX hNXR 0 _ hRotated hRotatedProper alpha hAlpha).
have hPullValue:=@pointed_holomorphic_pullback_centre_value R X Y NX NY hNXR hNY 0 0
  (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j (ltn_ord j)) P
  (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega j (ltn_ord j))
  (@holomorphic_prefix_projection_zero R X n omega j (ltn_ord j)) beta.
have hBetaValue:@HolomorphicGermValue.map R Y NY hNY 0 beta = 0.
  by rewrite -hPullValue hBeta.
have hBetaZeroJet:=(@holomorphic_germ_value_zeroth_jet R Y NY hNY 0 beta).1 hBetaValue.
have [k [hTop hLower]]:=@holomorphic_germ_first_nonzero_jet R Y NY hNY 0 beta hBetaNonzero.
have hPositive:(0<k)%N.
  case:k hTop hLower=>[|k] hTop hLower;last by [].
  exfalso;apply:hTop;exact:hBetaZeroJet.
exists beta;split;first by rewrite hBeta.
split;first exact:hBetaNonzero.
exists k;by split;last split.
Qed.
End Witness.
