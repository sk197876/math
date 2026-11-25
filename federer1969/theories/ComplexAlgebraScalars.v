(** Federer (1969), 1.6.6, pp. 26-27: complex scalar action on the real
    alternating algebra, used in the subalgebra and volume assertions.
    Scalars are the central constant coefficient forms. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CoefficientAction
  AlgebraUP TensorUP Bilinear ComplexScalarSealed ComplexCoefficientAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Scalars.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable U : lmodType R.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Local Notation A := (alternating_unital_algebra h2 U CR).
Local Notation c z := (@coefficient_form R U CR z).
Local Notation mul := (alg_mul A).

(** Source for [complex_algebra_scale]: Federer 1.6.6, p. 26,
    complex algebra structure of A^*(V,C). Scalar action as
    multiplication by the corresponding constant form. *)
Definition complex_algebra_scale (z : C) (a : A) : A := mul (c z) a.

(** Source for [complex_algebra_scaleE]: Federer 1.6.6,
    p. 26, complex scalar action. It multiplies every value by z. *)
Lemma complex_algebra_scaleE z a x : complex_algebra_scale z a x = z * a x.
Proof. exact: coefficient_product_leftE. Qed.

(** Source for [complex_algebra_scaleA]: Federer 1.6.6,
    p. 26, complex algebra structure. Associativity of scalar action. *)
Lemma complex_algebra_scaleA z w a :
  complex_algebra_scale z (complex_algebra_scale w a) = complex_algebra_scale (z*w) a.
Proof.
apply: hom_finite_ext => x.
rewrite [LHS]complex_algebra_scaleE [RHS]complex_algebra_scaleE.
by rewrite [complex_algebra_scale w a x]complex_algebra_scaleE mulrA.
Qed.

(** Source for [complex_algebra_scale1]: Federer 1.6.6,
    p. 26, complex algebra structure. One acts as the identity. *)
Lemma complex_algebra_scale1 a : complex_algebra_scale 1 a = a.
Proof. by apply: hom_finite_ext => x; rewrite complex_algebra_scaleE mul1r. Qed.

(** Source for [complex_algebra_scaleD]: Federer 1.6.6,
    p. 26, complex algebra structure. Distributivity over addition of forms. *)
Lemma complex_algebra_scaleD z a b :
  complex_algebra_scale z (a+b) = complex_algebra_scale z a + complex_algebra_scale z b.
Proof. exact: (bilDr (alg_bilinear A)). Qed.

(** Source for [complex_algebra_scalarD]: Federer 1.6.6,
    p. 26, complex algebra structure. Distributivity over addition of scalars. *)
Lemma complex_algebra_scalarD z w a :
  complex_algebra_scale (z+w) a = complex_algebra_scale z a + complex_algebra_scale w a.
Proof.
apply: hom_finite_ext => x.
rewrite [LHS]complex_algebra_scaleE hom_finite_addE.
by rewrite !complex_algebra_scaleE mulrDl.
Qed.

(** Source for [complex_algebra_scale_product_left]: Federer
    1.6.6, p. 26, complex algebra structure. Compatibility with
    multiplication in the first factor. *)
Lemma complex_algebra_scale_product_left z a b :
  complex_algebra_scale z (mul a b) = mul (complex_algebra_scale z a) b.
Proof. exact: (@alg_assoc R A). Qed.

(** Source for [complex_algebra_scale_product_right]: Federer
    1.6.6, p. 26, complex algebra structure. Compatibility with
    multiplication in the second factor. *)
Lemma complex_algebra_scale_product_right z a b :
  complex_algebra_scale z (mul a b) = mul a (complex_algebra_scale z b).
Proof.
rewrite /complex_algebra_scale !(@alg_assoc R A).
congr (mul _ _); exact: (@coefficient_central R h2 U CR (@mulrC C)).
Qed.

(** Source for [complex_algebra_scale_product]: Federer 1.6.6,
    p. 27, volume factor (i/2)^n. Two scalar factors can be combined
    across an alternating product. *)
Lemma complex_algebra_scale_product z w a b :
  mul (complex_algebra_scale z a) (complex_algebra_scale w b) =
  complex_algebra_scale (z*w) (mul a b).
Proof.
by rewrite -complex_algebra_scale_product_left
  -complex_algebra_scale_product_right complex_algebra_scaleA.
Qed.
End Scalars.
