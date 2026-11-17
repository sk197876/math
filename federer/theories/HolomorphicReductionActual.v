(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(2),
    p. 326: the original complex reduction loci use actual
    coordinate germs, prefix subrings, unitary pullbacks and ideals.
    The complex dimension n and its real dimension 2n remain distinct. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness LinearBasis
  ComplexOrderedBases UnitaryGroup HolomorphicGermRing HolomorphicCoordinateGermsSealed
  HolomorphicCoordinateSubringFamilySealed HolomorphicRotatedGermIdeal
  HolomorphicReductionLociUP HolomorphicReductionLociSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Actual.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Variable I:set G.
Local Notation gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega).
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Local Notation rotated:=(@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I).

(** Source for [holomorphic_reduction_actual_A]: original
    A_j with actual complex Q_j and I_g, 3.4.12, p. 339. *)
Definition holomorphic_reduction_actual_A:=@HolomorphicReductionLoci.A R X NX hNX n U e gamma Q rotated.
(** Source for [holomorphic_reduction_actual_B]: original
    B_(j+1) with actual complex directional tests, 3.4.12, p. 339. *)
Definition holomorphic_reduction_actual_B:=@HolomorphicReductionLoci.B R X NX hNX n U e gamma Q rotated.
(** Source for [holomorphic_reduction_actual_C]: original complex
    denominator relations in I_g, 3.4.12, p. 339. *)
Definition holomorphic_reduction_actual_C:=@HolomorphicReductionLoci.C R X NX hNX n U e gamma Q rotated.
(** Source for [holomorphic_reduction_actual_E]: original E_m
    over U(n), including m=n, 3.4.12, p. 339. *)
Definition holomorphic_reduction_actual_E:=@HolomorphicReductionLoci.E R X NX hNX n U e gamma Q rotated.

(** Source for [holomorphic_reduction_actual_laws]: all exact
    original complex reduction equations, 3.4.12, p. 339. *)
Lemma holomorphic_reduction_actual_laws:is_holomorphic_reduction_loci e gamma Q rotated
  holomorphic_reduction_actual_A holomorphic_reduction_actual_B holomorphic_reduction_actual_C holomorphic_reduction_actual_E.
Proof. exact:(@HolomorphicReductionLoci.laws R X NX hNX n U e gamma Q rotated). Qed.
End Actual.
