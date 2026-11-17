(** Federer (1969), 3.4.12, p. 339:
    U(n) is the actual subgroup of complex linear
    members of the real orthogonal group. Reuse the
    original action and both inverse identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  HermitianUP HermitianRealImaginary InnerMetric LinearBasis HomInner
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  TopologicalGroupUP IsotropyGroupTopology PointwiseCommutingLocusUP
  PointwiseCommutingLocusSealed PointwiseCommutingSubgroup UnitaryGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Subgroup.
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
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R XR B hB N e he)
  (@linear_group_inv R XR B hB N e he) (@linear_group_unit R XR B hB N e he)
  O mulO invO unitO.

(** Source for [unitary_group_subgroup]: the actual
    original unitary transformations are closed under identity,
    composition and inverse, 3.4.12, p. 339. *)
Theorem unitary_group_subgroup:
  is_subgroup mulO invO unitO (@unitary_group R X H hH N e he).
Proof.
apply:(@pointwise_commuting_subgroup O X (ComplexScalars.C R) mulO invO unitO action
  (fun (c:ComplexScalars.C R) (x:X)=>c*:x) (@unitary_group R X H hH N e he)
  (@PointwiseCommutingLocus.laws O X (ComplexScalars.C R) action
    (fun (c:ComplexScalars.C R) (x:X)=>c*:x))).
- exact:(@orthogonal_element_unit R XR B hB N e he mulO invO unitO hO).
- exact:(@orthogonal_element_mulE R XR B hB N e he mulO invO unitO hO).
- move=>g;exact:(@orthogonal_element_inv R XR B hB N e he mulO invO unitO hO g).1.
- move=>g;exact:(@orthogonal_element_inv R XR B hB N e he mulO invO unitO hO g).2.
Qed.
End Subgroup.
