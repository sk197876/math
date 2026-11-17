(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology HolomorphicGermRing HolomorphicReductionActual HolomorphicReductionLociUP.
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


(** Source for [holomorphic_reduction_E_all_index_tail]: the original
    B_j witnesses selected in the product proof of
    3.4.8(14), p. 336, with both E_m endpoints. *)
Theorem holomorphic_reduction_E_all_index_tail
    (I:set G)
    (m:'I_n.+1) (g:O):
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I m g ->
  forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.

Proof.
move=>hEm j hMJ.
have hMN:(m<n)%N:=leq_ltn_trans hMJ (ltn_ord j).
pose mi:'I_n:=Ordinal hMN.
have hIndex:widen_ord (leqnSn n) mi=m by apply:val_inj.
have hOriginal:@holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) mi) g.
  by rewrite hIndex.
exact:((holomorphic_reduction_E_membership (@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I) mi g).1 hOriginal).2.1 j hMJ.
Qed.

End Connections.
