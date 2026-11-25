(** Federer (1969), 1.10.4, p. 46: finite-sum representation and the
    definition of degree. Degree zero for the zero polynomial follows
    Federer. The representation is unique in characteristic zero. In other
    characteristics, the operation below is only the degree of the chosen
    representation; no independence from that choice is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Graded GradedSums GradedDegreeUP GradedDegree
  Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormIsomorphism SymmetricFormSum HomogeneousPolynomialFunctions
  SymmetricPolynomialEvaluation SymmetricPolynomialInjectivity PolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Representations.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation A := (S_star V W).
Local Notation G := (S_star_grading V W).

(** Source for [symmetric_polynomial_value_sum]: Federer 1.10.4,
    p. 46, supporting pointwise linearity on a finite family of forms. *)
Lemma symmetric_polynomial_value_sum (I : finType) (f : I -> A) x :
  symmetric_polynomial_value (\sum_i f i) x = \sum_i symmetric_polynomial_value (f i) x.
Proof.
elim/big_ind2: _=> [|a b c d ha hb|i _].
- by rewrite (linear0 (@symmetric_polynomial_value K V W)).
- rewrite linearD.
  change (symmetric_polynomial_value b x + symmetric_polynomial_value d x = a+c).
  by rewrite ha hb.
- by [].
Qed.

(** Source for [polynomial_finite_representation]: Federer
    1.10.4, p. 46, the exact finite-sum definition, with N=M+1
    and also allowing an empty representation of the zero polynomial. *)
Theorem polynomial_finite_representation (P : V -> W) :
  is_polynomial_function P <->
  exists N (f : forall m, S_m V W m),
    forall x, P x = \sum_(i < N) sform_polynomial_value (f i) x.
Proof.
split.
- move=> [f hf]; exists (grade_bound G f), (fun m => sform_component m f)=> x.
  rewrite hf; exact: symmetric_polynomial_value_bound x (@grade_boundP K A G f).
- move=> [N [f hf]].
  exists (\sum_(i < N) sform_include (f i))=> x.
  rewrite hf symmetric_polynomial_value_sum.
  apply: eq_bigr=> i _; exact: esym (symmetric_polynomial_value_include (f i) x).
Qed.

(** Source for [polynomial_book_representation]: Federer 1.10.4,
    p. 46, the displayed definition with terms m=0,...,M for
    a nonnegative integer M. This version includes the degree-zero
    term even when the polynomial is zero. *)
Theorem polynomial_book_representation (P : V -> W) :
  is_polynomial_function P <->
  exists M (f : forall m, S_m V W m),
    forall x, P x = \sum_(i < M.+1) sform_polynomial_value (f i) x.
Proof.
split.
- move=> [f hf]; exists (grade_bound G f), (fun m => sform_component m f)=> x.
  rewrite hf; apply: symmetric_polynomial_value_bound.
  exact: grade_bounded_mono (leqnSn _) (@grade_boundP K A G f).
- move=> [M [f hf]]; apply/polynomial_finite_representation.
  exists M.+1,f; exact: hf.
Qed.

(** Source for [polynomial_degree]: Federer 1.10.4, p. 46,
    the supremum of the nonzero homogeneous coefficient indices together
    with {0}, using the abstract sealed graded-degree operation. The
    selected representation is intrinsic under characteristic-zero uniqueness. *)
Definition polynomial_degree (P : PolynomialFunction V W) :=
  graded_degree G (polynomial_to_forms P).

(** Source for [polynomial_degreeP]: Federer 1.10.4, p. 46,
    the degree satisfies the stated supremum laws for its selected
    homogeneous representation. In characteristic zero that representation
    is unique, as proved separately. *)
Theorem polynomial_degreeP P :
  is_graded_degree G (polynomial_to_forms P) (polynomial_degree P).
Proof. exact: graded_degreeP. Qed.

(** Source for [polynomial_degree_from_forms]: Federer 1.10.4,
    p. 46, computing the degree from any given coefficient representation
    agrees with the intrinsic degree of the actual polynomial function. *)
Lemma polynomial_degree_from_forms (h0 : [pchar K] =i pred0) f :
  polynomial_degree (polynomial_from_forms f) = graded_degree G f.
Proof. by rewrite /polynomial_degree (polynomial_from_formsK h0). Qed.

(** Source for [polynomial_degree_zero]: Federer 1.10.4,
    p. 46, the zero polynomial has degree zero. *)
Lemma polynomial_degree_zero (h0 : [pchar K] =i pred0) :
  polynomial_degree (0 : PolynomialFunction V W) = 0%N.
Proof.
rewrite -(linear0 (@polynomial_from_forms K V W)) (polynomial_degree_from_forms h0).
exact: graded_degree_zero.
Qed.

(** Source for [polynomial_degree_representation]: Federer
    1.10.4, p. 46, a polynomial equals the sum of its homogeneous
    terms from degree zero through its intrinsic degree. *)
Theorem polynomial_degree_representation (P : PolynomialFunction V W) x :
  P x = \sum_(i < (polynomial_degree P).+1)
    sform_polynomial_value (sform_component i (polynomial_to_forms P)) x.
Proof.
have h := congr1 (fun Q : PolynomialFunction V W => Q x) (polynomial_to_formsK P).
rewrite polynomial_from_formsE in h; rewrite -h.
apply: symmetric_polynomial_value_bound; exact: graded_degree_bound.
Qed.
End Representations.
