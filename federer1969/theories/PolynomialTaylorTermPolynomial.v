(** Federer (1969), 1.10.4, p. 46, the assertion that each Taylor
    coefficient is itself a polynomial with values in the space of symmetric
    forms. The supporting argument below curries a linear contraction map
    through the already proved symmetric-power/form isomorphism. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Graded GradedComponents Hom HomogeneousHom
  BoundedHom SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFiniteContraction HomogeneousPolynomialFunctions PolynomialTaylorTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Curried.
Variable K : fieldType.
Variables V W : lmodType K.
Variables m i : nat.
Variable f : S_m V W m.
Local Notation U := (S_m V W i).
Local Notation E := (symmetric_power V (m-i)).

(** Source for [taylor_power_coefficient]: Federer 1.10.4,
    p. 46, the linear map on the symmetric (m-i)-power
    whose divided-power evaluation is the m-th contribution to S_i. *)
Definition taylor_power_coefficient (eta : E) : U :=
  sform_component i (symmetric_finite_contraction eta (sform_include f)).

(** Source for [taylor_power_coefficient_linear]: Federer
    1.10.4, p. 46, supporting linearity of the curried
    map by bilinearity of contraction. *)
Lemma taylor_power_coefficient_linear : linear taylor_power_coefficient.
Proof.
move=> a eta theta; rewrite /taylor_power_coefficient
  symmetric_finite_contraction_parameter_linear linearP; by [].
Qed.
HB.instance Definition _ := GRing.isLinear.Build K E U *:%R
  taylor_power_coefficient taylor_power_coefficient_linear.

(** Source for [taylor_term_representing_form]: Federer
    1.10.4, p. 46, a symmetric (m-i)-form with values
    in S_i representing the Taylor contraction term as a polynomial. *)
Definition taylor_term_representing_form : S_m V U (m-i) :=
  hom_to_sform (hom_of_linear (GRing.Linear.clone _ _ _ _ taylor_power_coefficient _)).

(** Source for [taylor_term_representing_formE]: Federer
    1.10.4, p. 46, the constructed coefficient form
    evaluates to the Taylor term on x^(m-i)/(m-i)!. *)
Lemma taylor_term_representing_formE x :
  sform_polynomial_value taylor_term_representing_form x = symmetric_taylor_term i f x.
Proof.
rewrite /sform_polynomial_value /taylor_term_representing_form
  /hom_to_sform homogeneous_sformK homogeneous_extendE hom_of_linearE.
change (taylor_power_coefficient
  (component (symmetric_grading V) (m-i) (symmetric_divided_vector_power x (m-i))) =
  taylor_power_coefficient (symmetric_divided_power_component x (m-i))).
congr (taylor_power_coefficient _); apply: val_inj.
change (grade (symmetric_grading V) (m-i) (symmetric_divided_vector_power x (m-i)) =
  symmetric_divided_vector_power x (m-i)).
exact: symmetric_divided_power_homogeneous.
Qed.

(** Source for [symmetric_taylor_term_polynomial]: Federer
    1.10.4, p. 46, supporting the polynomial nature
    of S_i: each contribution from an m-form is homogeneous
    polynomial of degree m-i with values in S_i. *)
Theorem symmetric_taylor_term_polynomial :
  is_homogeneous_polynomial (m-i) (fun x => symmetric_taylor_term i f x).
Proof.
exists taylor_term_representing_form=> x.
exact: esym (taylor_term_representing_formE x).
Qed.
End Curried.
