(** Federer (1969), 1.10.4, p. 46: the linear map from the graded sum of
    symmetric forms to polynomial functions. Existing abstract graded-sum
    infrastructure makes the evaluation independent of a chosen finite
    support bound. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Graded GradedSums Hom HomogeneousHom BoundedHom
  HomogeneousSum SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormSum HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Evaluation.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation A := (S_star V W).
Local Notation G := (S_star_grading V W).
Local Notation F := (GRing.Lmodule.clone K (V -> W) _).

(** Source for [polynomial_degree_evaluation]: Federer 1.10.4,
    p. 46, a term in the finite sum. Evaluate a graded form
    on the divided power of the specified degree. *)
Definition polynomial_degree_evaluation x m (f : A) :=
  f (symmetric_divided_vector_power x m).

(** Source for [polynomial_degree_evaluation_linear]: Federer
    1.10.4, p. 46, supporting linearity of one term in the sum. *)
Lemma polynomial_degree_evaluation_linear x m : linear (polynomial_degree_evaluation x m).
Proof. by move=> a f g; rewrite /polynomial_degree_evaluation hom_finite_addE hom_finite_scaleE. Qed.
HB.instance Definition _ x m := GRing.isLinear.Build K A W *:%R
  (polynomial_degree_evaluation x m) (polynomial_degree_evaluation_linear x m).

(** Source for [symmetric_polynomial_value]: Federer 1.10.4,
    p. 46, the displayed finite sum over homogeneous components.
    The graded sum evaluates exactly those components; its construction
    uses the proved finite-support bound and is independent of that bound. *)
Definition symmetric_polynomial_value (f : A) (x : V) : W :=
  graded_sum G (fun m => GRing.Linear.clone _ _ _ _ (polynomial_degree_evaluation x m) _) f.

(** Source for [symmetric_polynomial_value_linear]: Federer
    1.10.4, p. 46, the asserted linear map into the function space. *)
Lemma symmetric_polynomial_value_linear : linear (symmetric_polynomial_value : A -> F).
Proof.
move=> a f g; apply: funext=> x.
exact: graded_sum_linear.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K A F *:%R
  symmetric_polynomial_value symmetric_polynomial_value_linear.

(** Source for [symmetric_polynomial_value_homogeneous]: Federer
    1.10.4, p. 46, a homogeneous form contributes just its own
    divided-power evaluation. *)
Lemma symmetric_polynomial_value_homogeneous m (f : A) x :
  homogeneous G m f -> symmetric_polynomial_value f x = f (symmetric_divided_vector_power x m).
Proof. exact: graded_sum_homogeneous. Qed.

(** Source for [symmetric_polynomial_value_include]: Federer
    1.10.4, p. 46, agreement with the homogeneous-polynomial definition. *)
Lemma symmetric_polynomial_value_include m (f : S_m V W m) x :
  symmetric_polynomial_value (sform_include f) x = sform_polynomial_value f x.
Proof.
rewrite (symmetric_polynomial_value_homogeneous x (sform_include_homogeneous f)).
by [].
Qed.

(** Source for [symmetric_polynomial_value_bound]: Federer
    1.10.4, p. 46, the displayed finite sum may use any upper
    bound containing the nonzero homogeneous components. *)
Lemma symmetric_polynomial_value_bound f N x : grade_bounded G f N ->
  symmetric_polynomial_value f x =
    \sum_(i < N) sform_polynomial_value (sform_component i f) x.
Proof.
move=> hN; rewrite /symmetric_polynomial_value (graded_sum_on _ hN).
apply: eq_bigr=> i _.
rewrite -sform_componentK.
by [].
Qed.
End Evaluation.
