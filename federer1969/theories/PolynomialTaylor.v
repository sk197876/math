(** Federer (1969), 1.10.4, pp. 46-47: Taylor formulas for actual polynomial
    functions. The definition below is intrinsic; the proved contraction
    formula identifies it with Federer's S_i. The differential
    interpretation is deferred to 3.1.11, as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedSums GradedDegree Hom HomogeneousHom
  BoundedHom SymmetricForms SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation PolynomialFunctions
  PolynomialRepresentations PolynomialTaylorTerms PolynomialTaylorTermPolynomial
  PolynomialTaylorCoefficients PolynomialTaylorTransform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Taylor.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables V W : lmodType K.
Variable P : PolynomialFunction V W.
Local Notation f := (polynomial_to_forms P).
Local Notation N := (polynomial_degree P).+1.

(** Source for [polynomial_taylor_coefficient]: Federer
    1.10.4, p. 46, S_i(x), defined intrinsically
    from the unique finite form representation of P. *)
Definition polynomial_taylor_coefficient i x : S_m V W i :=
  sform_component i (symmetric_taylor_transform f x).

(** Source for [polynomial_taylor_coefficient_formula]: Federer
    1.10.4, p. 46, the displayed sum of right
    contractions with x^(m-i)/(m-i)! from m=i through degree P. *)
Theorem polynomial_taylor_coefficient_formula i x :
  polynomial_taylor_coefficient i x =
    taylor_coefficient N (fun m => sform_component m f) i x.
Proof.
apply: (@symmetric_taylor_transform_component K V W h0 f N i x).
exact: graded_degree_bound.
Qed.

(** Source for [polynomial_taylor_coefficient_is_polynomial]:
    Federer 1.10.4, p. 46, S_i is a polynomial
    function with values in the vector space of symmetric i-forms. *)
Theorem polynomial_taylor_coefficient_is_polynomial i :
  is_polynomial_function (polynomial_taylor_coefficient i).
Proof.
exists (taylor_coefficient_representation N (fun m => sform_component m f) i)=> x.
by rewrite polynomial_taylor_coefficient_formula taylor_coefficient_representationE.
Qed.

(** Source for [polynomial_taylor_formula]: Federer 1.10.4,
    p. 46, Taylor's formula P(x+v)=sum_i <v^i/i!,S_i(x)>.
    The sum includes degrees zero through degree P, even for P=0. *)
Theorem polynomial_taylor_formula x v :
  P (x+v) = \sum_(i < N) sform_polynomial_value (polynomial_taylor_coefficient i x) v.
Proof.
rewrite polynomial_degree_representation (@polynomial_taylor_collected K V W N (fun m => sform_component m f) h0 x v).
apply: eq_bigr=> i _; by rewrite polynomial_taylor_coefficient_formula.
Qed.

(** Source for [polynomial_taylor_translation]: Federer
    1.10.4, pp. 46-47, the displayed translation
    identity S_i(x+v)=sum_m v^(m-i)/(m-i)! contracted with S_m(x).
    The coefficient sum is finite and starts at m=i. *)
Theorem polynomial_taylor_translation i x v : (i<N)%N ->
  polynomial_taylor_coefficient i (x+v) =
    taylor_coefficient N (fun m => polynomial_taylor_coefficient m x) i v.
Proof.
move=> hi; apply: (@symmetric_taylor_coefficient_translation K V W h0 f N i x v) hi.
exact: graded_degree_bound.
Qed.
End Taylor.
