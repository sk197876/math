(** Federer (1969), 3.4.12, p. 339: the original
    unitary transformation as a complex linear map, specified
    by its actual underlying real action before opaque choice. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  LinearBasis OrthogonalGroupHaarMeasure UnitaryGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_unitary_complex_map]: exact agreement with
    the original unitary action, 3.4.12, p. 339. *)
Definition is_unitary_complex_map (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e)
    (g:@unitary_group R X H hH N e he) (L:Hom X X):Prop:=
  forall x,L x=@orthogonal_element_map R (restricted_space (ComplexScalars.embed R) X)
    (hermitian_real_part H) (hermitian_real_inner_product hH) N e he (set_val g) x.
