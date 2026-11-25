(** Federer (1969), 1.10.4, p. 46, polynomial nature of the Taylor
    coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedSums GradedDegree Hom HomogeneousHom
  BoundedHom SymmetricForms SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation PolynomialFunctions
  PolynomialRepresentations PolynomialTaylorTermPolynomial
  PolynomialTaylorCoefficients PolynomialTaylorTransform PolynomialTaylor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Bound.
Variable K : fieldType.
Variables V W : lmodType K.
Variable M : nat.
Variable f : forall m, S_m V W m.

(** Source for [taylor_coefficient_degree_bound]: Federer 1.10.4, p. 46,
    supporting degree information for the polynomial S_i. Directly
    formalises. *)
Lemma taylor_coefficient_degree_bound i :
  grade_bounded (S_star_grading V (S_m V W i))
    (taylor_coefficient_representation M.+1 f i) (M-i).+1.
Proof.
move=> j hj; rewrite /taylor_coefficient_representation linear_sum.
apply: big1=> m hm; rewrite sform_include_grade.
have hmM : (m<=M)%N by move: (ltn_ord m); rewrite ltnS.
have hmi : (m-i <= M-i)%N := leq_sub2r i hmM.
have hne : j != (m-i)%N by rewrite neq_ltn (leq_ltn_trans hmi hj) orbT.
by rewrite (negbTE hne).
Qed.
End Bound.

Section ActualCoefficient.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables V W : lmodType K.
Variable P : PolynomialFunction V W.

(** Source for [polynomial_taylor_coefficient_map]: Federer
    1.10.4, p. 46, S_i packaged as an actual
    polynomial function into the space of symmetric i-forms. *)
Definition polynomial_taylor_coefficient_map i : PolynomialFunction V (S_m V W i) :=
  polynomial_from_forms (taylor_coefficient_representation (polynomial_degree P).+1
    (fun m => sform_component m (polynomial_to_forms P)) i).

(** Source for [polynomial_taylor_coefficient_mapE]: Federer
    1.10.4, p. 46, the packaged function evaluates
    to the intrinsic Taylor coefficient S_i(x). *)
Lemma polynomial_taylor_coefficient_mapE i x :
  polynomial_taylor_coefficient_map i x = polynomial_taylor_coefficient P i x.
Proof.
rewrite /polynomial_taylor_coefficient_map polynomial_from_formsE
  taylor_coefficient_representationE.
exact: esym (polynomial_taylor_coefficient_formula h0 P i x).
Qed.

(** Source for [polynomial_taylor_coefficient_degree]: Federer 1.10.4, p.
    46. *)
Theorem polynomial_taylor_coefficient_degree i :
  (polynomial_degree (polynomial_taylor_coefficient_map i) <= polynomial_degree P-i)%N.
Proof.
rewrite /polynomial_taylor_coefficient_map (polynomial_degree_from_forms h0).
apply: graded_degree_le_of_bound; exact: taylor_coefficient_degree_bound.
Qed.
End ActualCoefficient.
