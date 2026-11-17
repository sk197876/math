(** Federer (1969), 3.4.12, p. 339:
    U(n) consists of all original complex linear isometries.
    Use the actual real orthogonal group and its original
    scalar-commuting locus, preserving the original topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis HomInner LinearGroupTopology LinearGroupSealed OrthogonalMaps
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure ComplexRealLinearMap
  PointwiseCommutingLocusUP PointwiseCommutingLocusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Unitary.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable e:'I_N->XR.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R XR B hB N e he).
Local Notation action:=(fun g:O=>@orthogonal_element_map R XR B hB N e he g).

(** Source for [unitary_group]: the original unitary
    isometry group of 3.4.12, p. 339.
    Its underlying transformations remain actual real orthogonal
    maps and its extra scalar equations are opaque. *)
Definition unitary_group:set O:=
  @PointwiseCommutingLocus.value O X (ComplexScalars.C R) action
    (fun (c:ComplexScalars.C R) (x:X)=>c*:x).

(** Source for [unitary_group_membership]: membership retains
    exactly the original complex-linearity equations, 3.4.12,
    p. 339. Real isometry is already part
    of the underlying orthogonal group. *)
Theorem unitary_group_membership g:
  unitary_group g <->is_complex_linear_real_map (action g).
Proof. exact:(@PointwiseCommutingLocus.laws O X (ComplexScalars.C R) action
  (fun (c:ComplexScalars.C R) (x:X)=>c*:x) g). Qed.

(** Source for [unitary_element_complex_map]: an actual
    member of U(n) has an actual complex linear
    carrier with precisely the original values, 3.4.12,
    p. 339. No complex map is postulated. *)
Theorem unitary_element_complex_map (g:unitary_group):
  exists L:Hom X X,forall x,L x=action (set_val g) x.
Proof.
apply:complex_real_linear_map_exists.
exact:(unitary_group_membership (set_val g)).1 (set_valP g).
Qed.

(** Source for [unitary_element_norm]: every original
    member preserves the Hermitian norm, 3.4.12,
    p. 339; reuse its actual real orthogonal law. *)
Theorem unitary_element_norm (g:unitary_group) x:
  inner_norm hB (action (set_val g) x)=inner_norm hB x.
Proof. exact:(orthogonal_map_norm hB hB (orthogonal_element_orthogonal (set_val g)) x). Qed.
End Unitary.
