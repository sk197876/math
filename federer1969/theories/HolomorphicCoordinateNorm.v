(** Federer (1969), 3.4.12, p. 339: the original complex
    coordinate spaces have the standard Hermitian norm and its
    original underlying real norm. Reuse the actual Chapter 1
    Hermitian product; no new coordinate or norm model is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates StandardHermitian HermitianRealImaginary InnerNorm HermitianComplexNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [holomorphic_coordinate_norm]: the original norm
    on C^m used in the coordinate projections replacing R^m
    in 3.4.8(1), p. 326, under 3.4.12, p. 339. *)
Definition holomorphic_coordinate_norm (R:realType) m:
    coordinate_space (ComplexScalars.C R) m->R:=
  inner_norm (hermitian_real_inner_product (@standard_hermitian_productP R m)).

(** Source for [holomorphic_coordinate_norm_laws]: the original
    standard norm satisfies its complex scalar laws, including
    dimension zero, as required in 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_norm_laws (R:realType) m:
  is_complex_norm (@holomorphic_coordinate_norm R m).
Proof. exact:(hermitian_complex_norm (@standard_hermitian_productP R m)). Defined.
