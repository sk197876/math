(** Federer (1969), 1.6.6, p. 26: complex scalar multiplication commutes
    with the alternating product. These supporting identities use the
    coefficient action of 1.4.4, p. 20. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CoefficientAction
  AlternatingCoefficientMap FormCoefficients ComplexCoefficientAlgebra
  ComplexFormConjugation ComplexScalarSealed ComplexScalarUP
  ComplexScalarLaws AlgebraUP TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section Products.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable U : lmodType R.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Local Notation A := (alternating_unital_algebra h2 U CR).
Local Notation fw := (form_wedge h2 (alg_bilinear CR)).

(** Source for [complex_form_scale_include]: Federer 1.6.6,
    p. 26, complex scalar action on A^*. A complex scalar acts by
    multiplication by the corresponding constant coefficient form. *)
Lemma complex_form_scale_include m z (a : A_m U CR m) :
  form_include (complex_scale_form z a) =
  alg_mul A (@coefficient_form R U CR z) (form_include a).
Proof.
rewrite /complex_scale_form form_coefficients_include.
apply: hom_finite_ext => x.
by rewrite A_star_coefficientsE coefficient_product_leftE.
Qed.

(** Source for [complex_scale_wedge_left]: Federer 1.6.6,
    p. 26, complex algebra structure. Complex scalar multiplication
    commutes with multiplication in the first argument. *)
Lemma complex_scale_wedge_left p q z (a : A_m U CR p) (b : A_m U CR q) :
  complex_scale_form z (fw a b) = fw (complex_scale_form z a) b.
Proof.
apply: (can_inj (@form_includeK R U CR (p+q))).
rewrite complex_form_scale_include !form_wedge_include complex_form_scale_include.
exact: (@alg_assoc R A).
Qed.

(** Source for [complex_scale_wedge_right]: Federer 1.6.6,
    p. 26, complex algebra structure. Complex scalar multiplication
    commutes with multiplication in the second argument. *)
Lemma complex_scale_wedge_right p q z (a : A_m U CR p) (b : A_m U CR q) :
  complex_scale_form z (fw a b) = fw a (complex_scale_form z b).
Proof.
apply: (can_inj (@form_includeK R U CR (p+q))).
rewrite complex_form_scale_include !form_wedge_include complex_form_scale_include.
change (alg_mul A (@coefficient_form R U CR z) (alg_mul A (form_include a) (form_include b)) =
  alg_mul A (form_include a) (alg_mul A (@coefficient_form R U CR z) (form_include b))).
rewrite !(@alg_assoc R A).
congr (alg_mul A _ _).
exact: (@coefficient_central R h2 U CR (@mulrC C)).
Qed.

(** Source for [complex_scale_formA]: Federer 1.6.6, p. 26,
    complex module structure. Supporting associativity of scalar action. *)
Lemma complex_scale_formA m z w (a : A_m U CR m) :
  complex_scale_form z (complex_scale_form w a) = complex_scale_form (z*w) a.
Proof.
apply: form_ext => t.
rewrite (complex_scale_formE z (complex_scale_form w a) t)
  (complex_scale_formE w a t) (complex_scale_formE (z*w) a t).
exact: mulrA.
Qed.

(** Source for [complex_scale_form1]: Federer 1.6.6, p. 26,
    complex module structure. The unit scalar acts as the identity. *)
Lemma complex_scale_form1 m (a : A_m U CR m) : complex_scale_form 1 a = a.
Proof. by apply: form_ext => t; rewrite complex_scale_formE mul1r. Qed.

(** Source for [complex_scale_formN1]: Federer 1.6.6, p. 26,
    even and odd conjugate-product formulas. Minus one negates a form. *)
Lemma complex_scale_formN1 m (a : A_m U CR m) : complex_scale_form (-1) a = -a.
Proof.
by apply: form_ext => t; rewrite complex_scale_formE mulN1r.
Qed.

(** Source for [complex_scale_formD]: Federer 1.6.6, p. 26,
    complex algebra structure. Distributivity over addition of forms. *)
Lemma complex_scale_formD m z (a b : A_m U CR m) :
  complex_scale_form z (a+b) = complex_scale_form z a + complex_scale_form z b.
Proof. exact: linearD. Qed.

(** Source for [complex_scale_formN]: Federer 1.6.6, p. 26,
    conjugate-product formulas. Compatibility with negation. *)
Lemma complex_scale_formN m z (a : A_m U CR m) :
  complex_scale_form z (-a) = - complex_scale_form z a.
Proof. exact: linearN. Qed.

(** Source for [complex_wedge_same_degree_commute]: Federer
    1.6.6, p. 26, even and odd conjugate-product formulas. Supporting
    graded commutation of two forms of the same degree. *)
Lemma complex_wedge_same_degree_commute m (a b : A_m U CR m) :
  fw a b = (-1 : R)^+(m * m) *: fw b a.
Proof.
apply: (can_inj (@form_includeK R U CR (m+m))).
rewrite linearZ.
change (form_include (fw a b) = (-1 : R)^+(m * m) *: form_include (fw b a)).
rewrite !form_wedge_include.
exact (@alternating_wedge_anticommutative R h2 U CR
  (alg_mul CR) (alg_bilinear CR) (@mulrC C) m m
  (form_include a) (form_include b) (form_include_homogeneous a) (form_include_homogeneous b)).
Qed.
End Products.
