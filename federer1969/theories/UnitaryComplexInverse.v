(** Federer (1969), 3.4.12, p. 339: the original
    unitary inverse is unitary. The real orthogonal inverse
    and scalar-commutation identity give both actual complex
    inverse equations. No inverse map is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  LinearBasis OrthogonalGroupHaarMeasure OrthogonalGroupTopology UnitaryGroup UnitaryComplexMapSealed
  ComplexRealLinearMap ComplexLinearInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [unitary_complex_inverse_exists]: both original
    inverse equations for every g in U(n), 3.4.12, p. 339. *)
Theorem unitary_complex_inverse_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he):
  exists h:@unitary_group R X H hH N e he,
    (forall x,@UnitaryComplexMap.value R X H hH N e he h
      (@UnitaryComplexMap.value R X H hH N e he g x)=x) /\
    (forall x,@UnitaryComplexMap.value R X H hH N e he g
      (@UnitaryComplexMap.value R X H hH N e he h x)=x).
Proof.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose B:=hermitian_real_part H;pose hB:=hermitian_real_inner_product hH.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R XR B hB N e he.
have [hLeft hRight]:=@orthogonal_element_inv R XR B hB N e he mulO invO unitO hO (set_val g).
have hComplex:=(@unitary_group_membership R X H hH N e he (set_val g)).1 (set_valP g).
have hInverseComplex:=complex_linear_real_inverse hRight hLeft hComplex.
have hMembership:=(@unitary_group_membership R X H hH N e he (invO (set_val g))).2 hInverseComplex.
pose h:@unitary_group R X H hH N e he:=exist _ (invO (set_val g)) (mem_set hMembership).
exists h;split=>x;rewrite !(@UnitaryComplexMap.laws R X H hH N e he).
- exact:hLeft.
- exact:hRight.
Qed.
