(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicLinear NormMetric SetGermUP CommutativeIdealUP NormFiniteLinearBound HolomorphicVarietyGermUP HolomorphicVarietyGermSeparation HolomorphicRotatedVanishingIdeal HolomorphicRotatedIdealRecovery HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyGermExistence FiniteHolomorphicVarietyUP FiniteHolomorphicLinearPullback UnitaryComplexMapSealed HolomorphicGermVanishingSealed ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology HolomorphicGermRing HolomorphicUnitaryPullback HolomorphicRotatedGermIdeal.
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



(** Source for [holomorphic_rotated_variety_representative]: the
    original representative of the rotated variety, extending
    3.4.8(13), p. 336, under 3.4.12, p. 339.
    Retain the actual unitary map and both original finite
    equation systems; use the proved original ideal recovery. *)
Theorem holomorphic_rotated_variety_representative
    (I:set [the comNzRingType of G]) (hI:is_finitely_generated_commutative_ideal I)
    (g:O) (hIg:is_finitely_generated_commutative_ideal
      (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g)) (U H:set X):
  U 0 ->@is_finite_holomorphic_variety R X NX hNXR U H ->
  I=@HolomorphicSetIdeal.value R X NX hNXR 0
    (@set_germ (Topological.clone (real_norm_metric_space hNXR) _) 0 H) ->
  @HolomorphicIdealVarietyGerm.value R X NX hNXR 0
    (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g) hIg =
  @set_germ (Topological.clone (real_norm_metric_space hNXR) _) 0
    ((@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR g) @^-1` H).
Proof.
move=>hU0 hH hIEquation.
pose T:=Topological.clone (real_norm_metric_space hNXR) _.
pose u:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR g.
pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
pose alpha:=@HolomorphicIdealVarietyGerm.value R X NX hNXR 0 Ig hIg.
have hOriginal:=@given_holomorphic_vanishing_ideal_variety_recovery R X NX hNXR 0 I hI
  (@set_germ T 0 H) hIEquation.
have hRecovered:=@holomorphic_rotated_ideal_variety_recovery R X Herm hHerm (n+n) eR heR
  I g hI hIg hOriginal.
have hAlpha:@is_holomorphic_variety_germ R X NX hNXR 0 alpha.
  exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNXR 0 Ig alpha
    (@HolomorphicIdealVarietyGerm.laws R X NX hNXR 0 Ig hIg)).
have hBound:=@norm_finite_linear_bounded R XR XR NX NX hNXR hNXR (n+n) eR heR (complex_hom_real u).
have hPreimage:@is_holomorphic_variety_germ R X NX hNXR 0 (@set_germ T 0 (u @^-1` H)).
  exists (u @^-1` U),(u @^-1` H);split;first by rewrite /= linear0.
  split;last exact:erefl.
  exact:finite_holomorphic_linear_pullback hBound hH.
apply:(holomorphic_variety_germ_ideal_injective hAlpha hPreimage).
rewrite -hRecovered hIEquation.
exact:holomorphic_rotated_vanishing_ideal.
Qed.
End Connections.
