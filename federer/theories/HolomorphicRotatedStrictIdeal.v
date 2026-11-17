(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
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



(** Source for [holomorphic_rotated_strict_ideal_witness]: the
    proper enlarged ideal remains proper under the original unitary
    coordinate map, extending 3.4.8(11), p. 334, in
    3.4.12, p. 339. Reuse actual pullback injectivity. *)
Theorem holomorphic_rotated_strict_ideal_witness (I J:set G) (g:O):
  (exists f,J f /\~I f) ->exists beta,
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR J g beta /\
    ~@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g beta.
Proof.
move=>[f [hJ hNotI]].
pose M:=@holomorphic_unitary_germ_map R X Herm hHerm (n+n) eR heR g.
exists (M f);split.
- apply/holomorphic_rotated_germ_ideal_membership;by exists f.
- move/holomorphic_rotated_germ_ideal_membership=>[alpha [hAlpha hValue]].
  have hEqual:alpha=f:=@holomorphic_unitary_germ_map_injective R X Herm hHerm (n+n) eR heR g alpha f hValue.
  apply:hNotI;by rewrite -hEqual.
Qed.
End Connections.
