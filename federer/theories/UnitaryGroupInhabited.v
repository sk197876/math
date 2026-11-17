(** Federer (1969), 3.4.12, p. 339: the identity
    belongs to the actual unitary group, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure UnitaryGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [unitary_group_inhabited]: an actual original
    unitary group element, used only to prove existence of
    the finite reduction minimum, 3.4.12, p. 339. *)
Theorem unitary_group_inhabited (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e):
  exists g:@unitary_group R X H hH N e he,True.
Proof.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R
  (restricted_space (ComplexScalars.embed R) X) (hermitian_real_part H)
  (hermitian_real_inner_product hH) N e he.
have hMember:@unitary_group R X H hH N e he unitO.
  apply/(@unitary_group_membership R X H hH N e he unitO)=>c x.
  by rewrite !(@orthogonal_element_unit R _ _ _ _ _ _ mulO invO unitO hO).
exists (exist _ unitO (mem_set hMember));exact:Logic.I.
Qed.
