(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicGermFormsUP HolomorphicGermJetZeroNegate ContinuousMultilinearUP ContinuousMultilinearSealed ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
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


(** Source for [holomorphic_reduction_B_contained_A]: an original
    positive directional witness is a nonzero original germ,
    extending 3.4.11, p. 338, under 3.4.12, p. 339.
    Apply the actual opaque form and zero-jet laws. *)
Theorem holomorphic_reduction_B_contained_A
    (I:classical_sets.set [the comNzRingType of G]) (j:'I_n) g:
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g ->
  @holomorphic_reduction_actual_A R X Herm hHerm n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g.
Proof.
have hLaws:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I.
move/(holomorphic_reduction_B_membership hLaws j g)=>[alpha [hAlpha [hQ [k [hPositive hDirection]]]]].
apply/(holomorphic_reduction_A_membership hLaws _ g).
split;first exact:ltn0Sn.
exists alpha;split;first exact:hAlpha.
split;first exact:hQ.
move=>hZero;apply:hDirection.
rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k alpha).
by rewrite hZero holomorphic_germ_jet_zero linear0.
Qed.
End Connections.
