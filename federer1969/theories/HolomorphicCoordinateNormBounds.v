(** Federer (1969), 3.4.12, p. 339: the original complex
    coordinate projection is bounded by the standard norm. Apply
    the existing Hermitian Cauchy inequality and original coordinate
    basis pairing; no new norm or coordinate model is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexScalarLaws ComplexModulus
  FiniteCoordinates StandardHermitian StandardHermitianBasisValues HermitianRealImaginary
  InnerNorm HermitianCauchy HolomorphicCoordinateNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
(** Source for [holomorphic_coordinate_unit_norm]: the original
    standard complex basis has unit norm by 1.8.2, p. 39,
    as used for the coordinate estimates in 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_unit_norm (R:realType) n (i:'I_n):
  @holomorphic_coordinate_norm R n (@coordinate_basis (ComplexScalars.C R) n i) = 1.
Proof.
apply:inner_norm_value;first exact:ler01.
rewrite expr1n /hermitian_real_part standard_hermitian_coordinate_basis_value
  /coordinate_basis ffunE eqxx.
by rewrite -(rmorph1 (ComplexScalars.embed R)) re_embed.
Qed.
(** Source for [holomorphic_coordinate_norm_bound]: each original
    coordinate modulus is at most the standard Hermitian norm,
    supporting the compact prefix estimates in 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_norm_bound (R:realType) n (i:'I_n)
    (x:coordinate_space (ComplexScalars.C R) n):
  complex_modulus (x i)<=@holomorphic_coordinate_norm R n x.
Proof.
have h:=@hermitian_cauchy R (coordinate_space (ComplexScalars.C R) n)
  (@standard_hermitian_product R n) (@standard_hermitian_productP R n)
  (@coordinate_basis (ComplexScalars.C R) n i) x.
rewrite standard_hermitian_coordinate_basis_value in h.
change (is_true (complex_modulus (x i)<=
  @holomorphic_coordinate_norm R n (@coordinate_basis (ComplexScalars.C R) n i)*
  @holomorphic_coordinate_norm R n x)) in h.
by rewrite holomorphic_coordinate_unit_norm mul1r in h.
Qed.
