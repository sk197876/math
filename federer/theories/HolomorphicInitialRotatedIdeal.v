(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    an actual leading polynomial of a rotated original
    ideal belongs to the rotated leading ideal. Actual
    orthogonal inverses and the already proved linear
    initial-polynomial transport supply the missing connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure HolomorphicGermUP HolomorphicGermRing
  HolomorphicRotatedGermIdeal HolomorphicUnitaryPullback HolomorphicUnitaryPullbackInverse
  HolomorphicInitialPolynomialGermUP PointedHolomorphicInitialPolynomialGerm HolomorphicInitialIdealSealed
  HolomorphicInitialIdealLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_rotated_ideal_member]:
    leading homogeneous polynomials commute with the original
    orthogonal substitutions in 3.4.12, p. 339, extending 3.4.11, p. 338.
    No equality of constructed ideals or choice of
    polynomial representatives is assumed. *)
Theorem holomorphic_initial_rotated_ideal_member (R:realType) (X:lmodType (ComplexScalars.C R))
  (B:X->X->ComplexScalars.C R) (hB:is_hermitian_product B) n (e:'I_n->X) (he:is_basis e)
  (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hB)) (complex_norm_real (hermitian_complex_norm hB)) 0))
  (g:@unitary_group R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he)) alpha beta:
  @holomorphic_rotated_germ_ideal R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he) I g alpha ->
  is_initial_polynomial_germ alpha beta ->
  @holomorphic_rotated_germ_ideal R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he)
    (@HolomorphicInitialIdeal.value R X (inner_norm (hermitian_real_inner_product hB)) (complex_norm_real (hermitian_complex_norm hB)) I) g beta.
Proof.
move=>hRotated hInitial.
pose NX:=inner_norm (hermitian_real_inner_product hB);pose hNX:=complex_norm_real (hermitian_complex_norm hB).
pose M:=fun g:@unitary_group R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he)=>
  @holomorphic_unitary_germ_map R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he) g.
have [delta [hDelta hAction]]:=(holomorphic_rotated_germ_ideal_membership I g alpha).1 hRotated.
have [h [hLeft hRight]]:=@holomorphic_unitary_germ_inverse_exists R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he) g.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU hRest]]]]]]]]:=
  @unitary_group_haar_exists R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he).
have [hMapLeft hMapRight]:=@unitary_complex_original_inverse R X B hB n e he
  mulO invO unitO hO mulU invU unitU hU h.
have hOnto y:exists x,@UnitaryComplexMap.value R X B hB (n+n)
    (ordered_real_basis e) (ordered_real_basisP he) h x=y.
  exists (@UnitaryComplexMap.value R X B hB (n+n)
    (ordered_real_basis e) (ordered_real_basisP he) (invU h) y);exact:hMapRight.
have hOriginal:=@pointed_holomorphic_initial_polynomial_germ R X X NX NX hNX hNX
  (@UnitaryComplexMap.value R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he) h) (M h)
  (@holomorphic_unitary_germ_map_specification R X B hB (n+n) (ordered_real_basis e) (ordered_real_basisP he) h) hOnto alpha beta hInitial.
have hSource:M h alpha=delta by rewrite -hAction hLeft.
rewrite hSource in hOriginal.
apply/(holomorphic_rotated_germ_ideal_membership _ g beta).
exists (M h beta);split;last exact:hRight.
exact:(@holomorphic_initial_ideal_contains R X NX hNX I delta (M h beta) hDelta hOriginal).
Qed.
