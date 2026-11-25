(** Federer (1969), 3.1.11, p. 223: the coordinate
    expansion of a symmetric differential in the dual monomials.
    The proof uses the divided monomial basis from 1.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Hom HomogeneousHom GradedComponents LinearBasis
  CoefficientCoordinates FiniteDualDimension SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricPairing
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricMonomialTuples
  SymmetricDividedMonomials SymmetricDividedBasis SymmetricCoordinateDualBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_form_coordinate_expansion]: a vector-valued
    symmetric k-form is the sum of its monomial values times
    the scalar dual monomials divided by alpha!, the algebraic
    expansion used in Federer 3.1.11, p. 223. Only the
    source has finite dimension; the target is arbitrary. *)
Theorem symmetric_form_coordinate_expansion (K : fieldType)
    (h0 : [pchar K]=i pred0) (X Y : lmodType K) n (e : 'I_n->X)
    (he : is_basis e) k (phi : S_m X Y k) (t : k.-tuple X) :
  phi t=\sum_(alpha : symmetric_indices n k)
    ((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
      ((symmetric_coordinate_basis_form he k alpha t : K)*:
        phi (symmetric_monomial_tuple e alpha)).
Proof.
pose hd := symmetric_divided_basis h0 he k.
have hh := congr1 (fun L : Hom (symmetric_power X k) Y=>L (symmetric_tuple_component t))
  (finite_Hom_coefficients hd (sform_to_hom phi)).
rewrite sform_to_hom_tuple hom_sum_coefficientsE in hh.
rewrite hh; apply: eq_bigr=>alpha _.
rewrite hom_with_coefficientE
  -(@symmetric_coordinate_basis_to_hom K h0 X n e he k alpha)
  sform_to_hom_tuple sform_to_homE symmetric_divided_basis_vectorE
  /symmetric_divided_monomial linearZ.
change ((symmetric_coordinate_basis_form he k alpha t : K)*:
  (((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
    sform_homogeneous phi (symmetric_monomial e (symmetric_indices_unbound alpha)))=
  ((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
    ((symmetric_coordinate_basis_form he k alpha t : K)*:
      phi (symmetric_monomial_tuple e alpha))).
by rewrite symmetric_monomial_form_value !scalerA mulrC.
Qed.
