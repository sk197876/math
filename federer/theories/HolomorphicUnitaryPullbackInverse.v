(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2),
    p. 326: the original unitary germ homomorphism is
    invertible. Reuse actual unitary inversion and the pointed
    pullback retraction theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary
  HermitianComplexNorm InnerNorm HilbertFormCompactness LinearBasis UnitaryGroup UnitaryComplexMapSealed
  UnitaryComplexInverse HolomorphicGermUP HolomorphicGermRing HolomorphicUnitaryPullback
  PointedHolomorphicPullbackRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_unitary_germ_inverse_exists]: both
    inverse equations in the original holomorphic germ ring,
    3.4.12, p. 339. *)
Theorem holomorphic_unitary_germ_inverse_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he):
  exists h:@unitary_group R X H hH N e he,
    (forall alpha,@holomorphic_unitary_germ_map R X H hH N e he h
      (@holomorphic_unitary_germ_map R X H hH N e he g alpha)=alpha) /\
    (forall alpha,@holomorphic_unitary_germ_map R X H hH N e he g
      (@holomorphic_unitary_germ_map R X H hH N e he h alpha)=alpha).
Proof.
have [h [hLeft hRight]]:=unitary_complex_inverse_exists g.
pose NX:=inner_norm (hermitian_real_inner_product hH).
pose hNX:=complex_norm_real (hermitian_complex_norm hH).
pose u:=@UnitaryComplexMap.value R X H hH N e he g.
pose v:=@UnitaryComplexMap.value R X H hH N e he h.
pose P:=@holomorphic_unitary_germ_map R X H hH N e he g.
pose Q:=@holomorphic_unitary_germ_map R X H hH N e he h.
have hP:=@holomorphic_unitary_germ_map_specification R X H hH N e he g.
have hQ:=@holomorphic_unitary_germ_map_specification R X H hH N e he h.
exists h;split.
- exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNX hNX 0 0 u v P Q hP hQ hRight).
- exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNX hNX 0 0 v u Q P hQ hP hLeft).
Qed.
