(** Federer (1969), 1.10.3, p. 45: the two monomial interior formulas and
    their zero cases. The coefficient computations below prove Federer's
    displayed formulas using the monomial bases and diagonal already
    established in 1.9. *)

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear Graded Hom HomogeneousHom BoundedHom
  LinearBasis SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials
  SymmetricMonomialBasis SymmetricDividedMonomials SymmetricDividedBasis
  SymmetricExponentBox SymmetricForms SymmetricFormExtension
  SymmetricFormIsomorphism SymmetricFormSum SymmetricPairing
  SymmetricMonomialCoordinates SymmetricDualMonomialProducts
  SymmetricDualMonomialBasis SymmetricMonomialProducts
  SymmetricRightInteriorHom SymmetricRightInterior SymmetricLeftInteriorHom
  SymmetricLeftInterior SymmetricRightMonomialContraction SymmetricLeftMonomialContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Formulas.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable omega : 'I_n -> S_m V K^o 1.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) = if j == i then 1 else 0.
Local Notation E := (symmetric_space V).
Local Notation M := (symmetric_one_form_monomial omega).
Local Notation C := (symmetric_monomial_coordinate he).

(** Source for [symmetric_divided_dual_monomial_coordinate]: Federer
    1.10.3, p. 45, supporting normalization: the homogeneous linear
    map corresponding to omega^beta/beta! is the ordinary monomial
    coordinate C_beta. This uses the actual product identity of 1.10.2. *)
Lemma symmetric_divided_dual_monomial_coordinate b :
  ((symmetric_multi_factorial b)%:R : K)^-1 *: (hom_finite_val (M b)) = C b.
Proof.
rewrite (symmetric_one_form_monomial_coordinate he h0 hd).
apply: hom_ext=> x; rewrite hom_scaleE symmetric_coordinate_full_formE.
change ((symmetric_multi_factorial b)%:R^-1 *
  ((symmetric_multi_factorial b)%:R * C b x) = C b x).
by rewrite mulrA mulVf ?mul1r //; exact: (@symmetric_multi_factorial_nonzero K h0).
Qed.

(** Source for [symmetric_right_interior_monomial_formula]: Federer
    1.10.3, p. 45, first displayed formula, evaluated as a linear map:
    e^alpha contracted with omega^beta/beta! equals
    omega^(beta-alpha)/(beta-alpha)! when alpha<=beta and zero otherwise.
    The homogeneous maps identify the forms uniquely by 1.10.1. *)
Theorem symmetric_right_interior_monomial_formula p q (hpq : (p<=q)%N)
    (a : symmetric_indices n p) (b : symmetric_indices n q) x :
  sform_homogeneous
    (symmetric_right_interior hpq (symmetric_finite_monomial e a)
      (((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : K)^-1 *:
        symmetric_dual_monomial omega b)) x =
  if symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b)
  then ((symmetric_multi_factorial
    (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)))%:R : K)^-1 *
    M (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)) x
  else 0.
Proof.
rewrite symmetric_right_interior_homogeneousE linearZ hom_m_scaleE.
change (((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : K)^-1 *
  sform_include (symmetric_dual_monomial omega b)
    (symmetric_product x (symmetric_monomial e (symmetric_indices_unbound a))) = if symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b)
  then ((symmetric_multi_factorial
    (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)))%:R : K)^-1 *
    M (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)) x
  else 0).
rewrite (symmetric_dual_monomial_include he h0 hd).
have hb := congr1 (fun f : Hom E K^o => f
  (symmetric_product x (symmetric_monomial e (symmetric_indices_unbound a))))
  (symmetric_divided_dual_monomial_coordinate (symmetric_indices_unbound b)).
rewrite hom_scaleE in hb.
change (((symmetric_multi_factorial (symmetric_indices_unbound b))%:R : K)^-1 *
  M (symmetric_indices_unbound b)
    (symmetric_product x (symmetric_monomial e (symmetric_indices_unbound a))) =
  C (symmetric_indices_unbound b)
    (symmetric_product x (symmetric_monomial e (symmetric_indices_unbound a)))) in hb.
rewrite hb.
change (symmetric_right_interior_hom (symmetric_monomial e (symmetric_indices_unbound a))
  (C (symmetric_indices_unbound b)) x = if symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b)
  then ((symmetric_multi_factorial
    (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)))%:R : K)^-1 *
    M (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a)) x
  else 0).
rewrite symmetric_right_monomial_coordinate.
case: (symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b))=> //=.
exact: esym (congr1 (fun f : Hom E K^o => f x)
  (symmetric_divided_dual_monomial_coordinate _)).
Qed.

(** Source for [symmetric_left_interior_monomial_formula]: Federer
    1.10.3, p. 45, second displayed formula:
    (e^beta/beta!) contracted with omega^alpha equals
    e^(beta-alpha)/(beta-alpha)! when alpha<=beta, and zero otherwise.
    Component inclusion is injective, so this states equality of the
    actual vectors in degree q-p without an implicit degree cast. *)
Theorem symmetric_left_interior_monomial_formula p q (hpq : (p<=q)%N)
    (a : symmetric_indices n p) (b : symmetric_indices n q) :
  component_val (symmetric_left_interior hpq (symmetric_divided_basis_vector e b)
    (symmetric_dual_monomial omega a)) =
  if symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b)
  then symmetric_divided_monomial e
    (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a))
  else 0.
Proof.
rewrite symmetric_left_interiorE symmetric_divided_basis_vectorE.
change (symmetric_left_interior_hom
  (symmetric_divided_monomial e (symmetric_indices_unbound b))
  (sform_include (symmetric_dual_monomial omega a)) = if symmetric_multi_le (symmetric_indices_unbound a) (symmetric_indices_unbound b)
  then symmetric_divided_monomial e
    (symmetric_multi_difference (symmetric_indices_unbound b) (symmetric_indices_unbound a))
  else 0).
rewrite (symmetric_dual_monomial_include he h0 hd)
  (symmetric_one_form_monomial_coordinate he h0 hd).
exact (@symmetric_left_monomial_coordinate K h0 V n e he
  (symmetric_indices_unbound a) (symmetric_indices_unbound b)).
Qed.
End Formulas.
