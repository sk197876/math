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


(** Source for [holomorphic_rotated_ideal_intersection]: the ideal
    membership of the original product witness in
    3.4.8(14), p. 336. This supporting identity
    holds for arbitrary original subsets of the germ ring. *)
Theorem holomorphic_rotated_ideal_intersection
    (I J:set G)
    (g:O):
  @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR (I `&` J) g=
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g `&`
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR J g.

Proof.
apply/seteqP;split=>phi.
- move/holomorphic_rotated_germ_ideal_membership=>[alpha [[hI hJ] hMap]].
  split;apply/holomorphic_rotated_germ_ideal_membership;exists alpha;by split.
- move=>[/holomorphic_rotated_germ_ideal_membership[alpha [hI hAlpha]]
    /holomorphic_rotated_germ_ideal_membership[beta [hJ hBeta]]].
  have hEqual:alpha=beta.
    apply:(@holomorphic_unitary_germ_map_injective R X Herm hHerm (n+n) eR heR g).
    exact:eq_trans hAlpha (esym hBeta).
  apply/holomorphic_rotated_germ_ideal_membership;exists alpha;split;last exact:hAlpha.
  split;first exact:hI;by rewrite hEqual.
Qed.

End Connections.
