(** Federer (1969), 3.4.12, p. 339: the proved
    scalar-commuting equation supplies the unique original complex
    linear carrier. Reuse the actual unitary-group theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  LinearBasis OrthogonalGroupHaarMeasure UnitaryGroup UnitaryComplexMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [unitary_complex_map_exists]: every original
    unitary action has its complex carrier, 3.4.12, p. 339. *)
Theorem unitary_complex_map_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he):
  exists L:Hom X X,is_unitary_complex_map g L.
Proof. exact:(@unitary_element_complex_map R X H hH N e he g). Qed.

(** Source for [unitary_complex_map_unique]: the original real
    action determines its complex carrier, 3.4.12, p. 339. *)
Lemma unitary_complex_map_unique (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he) (L M:Hom X X):
  is_unitary_complex_map g L ->is_unitary_complex_map g M ->L=M.
Proof. move=>hL hM;apply:hom_ext=>x;by rewrite hL hM. Qed.
