(** Federer (1969), 3.4.12, p. 339: the original standard
    complex coordinate basis is Hermitian orthonormal. This connection
    evaluates the existing product of 1.8.2, p. 39; it introduces
    no replacement product or new coordinate model. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCoefficientAlgebra
  HermitianUP HermitianRealImaginary HermitianComplexLinearity StandardHermitian ComplexOrderedBases
  LinearBasis FiniteCoordinates OrthonormalFamilies InnerNorm InnerProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [standard_hermitian_coordinate_basis_value]: the
    original coordinate functional is the Hermitian pairing with its
    basis vector, supporting 3.4.12, p. 339. *)
Lemma standard_hermitian_coordinate_basis_value (R:realFieldType) n
    (v:coordinate_space (ComplexScalars.C R) n) (i:'I_n):
  standard_hermitian_product (@coordinate_basis (ComplexScalars.C R) n i) v=v i.
Proof.
rewrite /standard_hermitian_product (bigD1 i) //= /coordinate_basis ffunE eqxx.
have hOne:@conjugate R 1= 1 by rewrite -(rmorph1 (ComplexScalars.embed R)) conjugate_real.
have hZero:@conjugate R 0=0 by rewrite -(rmorph0 (ComplexScalars.embed R)) conjugate_real.
rewrite hOne mul1r.
under eq_bigr do rewrite ffunE.
have hTail:(\sum_(j:'I_n|j!=i) conjugate ((if j==i then 1 else 0):ComplexScalars.C R)*v j)=0.
  apply:big1=>j hj;by rewrite (negbTE hj) hZero mul0r.
by rewrite hTail addr0.
Qed.

(** Source for [standard_hermitian_basis_orthonormal]: the actual
    standard coordinate basis satisfies every Hermitian orthonormal
    equation, including dimension zero, 3.4.12, p. 339. *)
Lemma standard_hermitian_basis_orthonormal (R:realFieldType) n:
  orthonormal_family (@standard_hermitian_product R n) (@coordinate_basis (ComplexScalars.C R) n).
Proof.
move=>i j;rewrite standard_hermitian_coordinate_basis_value /coordinate_basis ffunE.
by rewrite eq_sym.
Qed.
