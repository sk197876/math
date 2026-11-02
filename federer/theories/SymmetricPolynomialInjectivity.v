(** Federer (1969), 1.10.4, p. 46: uniqueness of all homogeneous coefficient
    forms. Restriction to scalar multiples of a fixed vector reduces this to
    the locally proved univariate coefficient uniqueness; the polarization
    formula then recovers each form. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Graded GradedSums Hom HomogeneousHom BoundedHom
  HomogeneousSum SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Injectivity.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables V W : lmodType K.
Local Notation A := (S_star V W).
Local Notation G := (S_star_grading V W).

(** Source for [symmetric_polynomial_zero_coefficients]: Federer
    1.10.4, p. 46, vanishing of P implies that every homogeneous
    coefficient form vanishes. This includes degree zero and arbitrary
    dimensions of the input and coefficient spaces. *)
Theorem symmetric_polynomial_zero_coefficients (f : A) :
  (forall x, symmetric_polynomial_value f x = 0) ->
  forall i, sform_component i f = 0.
Proof.
move=> hf i.
pose N := grade_bound G f.
have hN : grade_bounded G f N := @grade_boundP K A G f.
case hi: (i<N)%N.
- apply/(sform_polynomial_zero_iff h0)=> x.
  apply: (@finite_power_coefficients_zero K h0 W N
    (fun j => sform_polynomial_value (sform_component j f) x)) hi=> t.
  have ht := hf (t *: x).
  rewrite (symmetric_polynomial_value_bound _ hN) in ht.
  move: ht.
  under eq_bigr do rewrite sform_polynomial_scale_argument.
  by [].
- apply: (can_inj (@sform_includeK K V W i)).
  rewrite sform_componentK linear0.
  apply: hN; by rewrite leqNgt hi.
Qed.

(** Source for [symmetric_polynomial_zero_iff]: Federer 1.10.4,
    p. 46, the complete vanishing criterion for the finite graded sum. *)
Theorem symmetric_polynomial_zero_iff (f : A) :
  (forall x, symmetric_polynomial_value f x = 0) <-> f=0.
Proof.
split.
- move=> hf; apply: symmetric_form_sum_ext=> i.
  by rewrite (symmetric_polynomial_zero_coefficients hf) linear0.
- move=> -> x; by rewrite (linear0 (@symmetric_polynomial_value K V W)).
Qed.

(** Source for [symmetric_polynomial_injective]: Federer 1.10.4,
    p. 46, uniqueness giving the asserted linear isomorphism with
    actual polynomial functions. *)
Theorem symmetric_polynomial_injective : injective (@symmetric_polynomial_value K V W).
Proof.
move=> f g hfg.
have hz : f-g=0.
  apply/(symmetric_polynomial_zero_iff)=> x.
  have he := congr1 (fun F : V -> W => F x) hfg.
  rewrite linearB.
  change (symmetric_polynomial_value f x - symmetric_polynomial_value g x = 0).
  by rewrite he subrr.
by move/eqP: hz; rewrite subr_eq0=> /eqP.
Qed.
End Injectivity.
