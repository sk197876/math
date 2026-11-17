(** Federer (1969), 3.4.12, p. 339: opaque complex
    carriers of the original unitary transformations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets functions reals boolp.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP
  LinearBasis UnitaryGroup UnitaryComplexMapUP UnitaryComplexMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type UnitaryComplexMapSignature.
(** Source for [value]: the original unitary complex map,
    3.4.12, p. 339. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he),Hom X X.
(** Source for [laws]: exact original real action,
    3.4.12, p. 339. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he),
  is_unitary_complex_map g (@value R X H hH N e he g).
End UnitaryComplexMapSignature.
Module UnitaryComplexMap:UnitaryComplexMapSignature.
(** Source for [value]: hidden choice from proved existence,
    3.4.12, p. 339. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he):=
  projT1 (cid (@unitary_complex_map_exists R X H hH N e he g)).
(** Source for [laws]: the hidden carrier retains the
    independent action equation, 3.4.12, p. 339. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he):
  is_unitary_complex_map g (@value R X H hH N e he g).
Proof. exact:(projT2 (cid (@unitary_complex_map_exists R X H hH N e he g))). Qed.
End UnitaryComplexMap.
