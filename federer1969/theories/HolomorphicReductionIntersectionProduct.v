(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology HolomorphicGermRing HolomorphicRotatedGermIdeal HolomorphicRotatedIdealIntersection
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicCoordinateSubringFamilyUP HolomorphicPrefixGermSubringLaws CommutativeSubringUP CommutativeIdealUP
  HolomorphicVanishingIdealSealed HolomorphicVanishingIdealLaws HolomorphicGermValueSealed
  HolomorphicGermValueZerothJet HolomorphicGermJetsSealed HolomorphicDirectionalProductNonzero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Connections.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).


(** Source for [holomorphic_reduction_intersection_product]: the product
    argument for B_j in 3.4.8(14), p. 336.
    Both original ideals are proper, so their actual
    witnesses vanish at the original centre. *)
Theorem holomorphic_reduction_intersection_product
    (I J:set [the comNzRingType of G])
    (j:'I_n) (g:O):
  is_commutative_ideal I ->~I 1 ->is_commutative_ideal J ->~J 1 ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega J j g ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega (I `&` J) j g.

Proof.
move=>hI hIProper hJ hJProper hBI hBJ.

pose A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
pose Jg:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR J g.
pose Q:=@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega.
have hILaws:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I.
have hJLaws:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega J.
have [alpha [hAlpha [hAlphaQ hAlphaJet]]]:=(holomorphic_reduction_B_membership hILaws j g).1 hBI.
have [beta [hBeta [hBetaQ hBetaJet]]]:=(holomorphic_reduction_B_membership hJLaws j g).1 hBJ.
have hIg:=@holomorphic_rotated_germ_ideal_is_ideal R X Herm hHerm (n+n) eR heR I g hI.
have hJg:=@holomorphic_rotated_germ_ideal_is_ideal R X Herm hHerm (n+n) eR heR J g hJ.
have hIgProper:=@holomorphic_rotated_germ_ideal_proper R X Herm hHerm (n+n) eR heR I g hIProper.
have hJgProper:=@holomorphic_rotated_germ_ideal_proper R X Herm hHerm (n+n) eR heR J g hJProper.
have hZeroth (K:set A) (hK:is_commutative_ideal K) (hKProper:~K 1) phi (hPhi:K phi):
    @HolomorphicGermJets.value R X NX hNXR 0 0%N phi=0.
  apply:(@holomorphic_germ_value_zeroth_jet R X NX hNXR 0 phi).1.
  apply/(@HolomorphicVanishingIdeal.laws R X NX hNXR 0 phi).
  exact:(@holomorphic_proper_ideal_vanishes R X NX hNXR 0 K hK hKProper phi hPhi).
have hProductJet:=@holomorphic_directional_product_nonzero R X NX hNX alpha beta (e j)
  (hZeroth Ig hIg hIgProper alpha hAlpha) (hZeroth Jg hJg hJgProper beta hBeta) hAlphaJet hBetaJet.
have hProductQ:Q (j:nat).+1 (alpha*beta).
  have hFamily:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
  have hSubring:is_commutative_subring (Q (j:nat).+1).
    rewrite /Q (holomorphic_coordinate_subring_family_member hFamily (ltn_ord j)).
    exact:(@holomorphic_prefix_germ_subring_laws R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j)).
  exact:(@commutative_subring_multiply A (Q (j:nat).+1) hSubring alpha beta hAlphaQ hBetaQ).
apply:(holomorphic_reduction_B_membership (@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega (I `&` J)) j g).2.
exists (alpha*beta);split.
- rewrite holomorphic_rotated_ideal_intersection;split.
  + rewrite mulrC;exact:(@commutative_ideal_mul A Ig hIg beta alpha hAlpha).
  + exact:(@commutative_ideal_mul A Jg hJg alpha beta hBeta).
by split.
Qed.

End Connections.
