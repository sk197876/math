(** Federer (1969), 3.4.12, p. 339: each original unitary
    transformation preserves the full Hermitian product. Its actual
    real isometry and complex-linearity laws determine both scalar
    coordinates; no extra preservation premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  HermitianUP HermitianRealImaginary HermitianComplexLinearity InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  UnitaryGroup UnitaryComplexMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Preservation.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable r:'I_N->XR.
Variable hr:is_basis r.
Local Notation O:=(@orthogonal_group R XR B hB N r hr).
Local Notation U:=(@unitary_group R X H hH N r hr).
Local Notation L:=(fun g:U=>@UnitaryComplexMap.value R X H hH N r hr g).

(** Source for [unitary_element_hermitian]: the full original
    Hermitian isometry equation, supporting 3.4.12, p. 339. *)
Theorem unitary_element_hermitian (g:U) v w:H (L g v) (L g w)=H v w.
Proof.
have hReal x y:B (L g x) (L g y)=B x y.
  rewrite !(@UnitaryComplexMap.laws R X H hH N r hr).
  exact:(@orthogonal_element_inner R XR B hB N r hr (set_val g) x y).
apply:ComplexScalarTheory.coordinates_injective.
- exact:hReal.
- change (hermitian_imaginary_part H (L g v) (L g w)=hermitian_imaginary_part H v w).
  rewrite !(@hermitian_imaginary_rotation R X H hH).
  have hComm:(ComplexScalars.ii R)*:(L g v)=L g ((ComplexScalars.ii R)*:v) by rewrite linearZ.
  rewrite hComm;exact:hReal.
Qed.
End Preservation.
