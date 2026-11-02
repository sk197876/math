(** Federer (1969), 1.10.2, p. 45: actual products of the dual one-forms.
    Products are formed with the previously defined symmetric
    multiplication. The normalized-coordinate calculation proves their
    values. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded Hom BoundedHom LinearBasis ScalarCoefficients
  SymmetricAlgebra SymmetricGrading SymmetricLowPowers SymmetricMultiIndices
  SymmetricMonomials SymmetricMultiIndexAddition SymmetricUnitMultiIndices
  SymmetricExponentWords SymmetricForms SymmetricFormSum SymmetricFormProduct
  SymmetricFormUnit SymmetricPairing SymmetricMonomialCoordinates
  SymmetricCoordinateProducts SymmetricCoordinateOneForms SymmetricCoordinateUnit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Products.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> S_m V K^o 1.

(** Source for [symmetric_one_form_word]: Federer 1.10.2,
    p. 45, multiply a specified finite list of the one-forms,
    with coefficient one as the empty product. *)
Definition symmetric_one_form_word (s : seq 'I_n) : S_star V K^o :=
  foldr (symmetric_forms_product (scalar_bilinear K))
    (@symmetric_coefficient_form K V K^o 1) [seq sform_include (omega i) | i <- s].

(** Source for [symmetric_one_form_monomial]: Federer 1.10.2,
    p. 45, the displayed product omega^alpha: alpha_i repeated
    copies of each omega_i, ordered by the basis coordinate enumeration. *)
Definition symmetric_one_form_monomial (a : symmetric_multi_index n) : S_star V K^o :=
  symmetric_one_form_word (symmetric_monomial_word idfun a).

Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis h0 : [pchar K] =i pred0.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) = if j == i then 1 else 0.
Local Notation M := (symmetric_coordinate_full_form he).

(** Source for [symmetric_one_form_word_coordinate]: Federer
    1.10.2, p. 45, supporting induction: the product of the listed
    dual one-forms equals the normalized coordinate at their exponent count. *)
Lemma symmetric_one_form_word_coordinate s :
  symmetric_one_form_word s = M (symmetric_exponent_word_count s).
Proof.
elim: s=> [|i s ih].
- by rewrite symmetric_exponent_word_count_nil symmetric_coordinate_zero_coefficient.
- change (symmetric_forms_product (scalar_bilinear K) (sform_include (omega i))
    (symmetric_one_form_word s) = M (symmetric_exponent_word_count (i::s))).
  rewrite ih (@symmetric_coordinate_one_form_include K h0 V n e he omega hd i)
    (@symmetric_coordinate_product K h0 V n e he).
  by rewrite symmetric_exponent_word_count_cons.
Qed.

(** Source for [symmetric_one_form_monomial_coordinate]: Federer
    1.10.2, p. 45, identify the actual product omega^alpha
    with the normalized monomial coordinate, establishing the claimed pairing. *)
Theorem symmetric_one_form_monomial_coordinate a :
  symmetric_one_form_monomial a = M a.
Proof.
by rewrite /symmetric_one_form_monomial symmetric_one_form_word_coordinate
  symmetric_exponent_word_count_monomial.
Qed.

(** Source for [symmetric_one_form_monomial_graded]: Federer
    1.10.2, p. 45, the product omega^alpha has degree |alpha|. *)
Lemma symmetric_one_form_monomial_graded a :
  homogeneous (S_star_grading V K^o) (symmetric_multi_degree a)
    (symmetric_one_form_monomial a).
Proof. rewrite symmetric_one_form_monomial_coordinate; exact: symmetric_coordinate_full_form_graded. Qed.
End Products.
