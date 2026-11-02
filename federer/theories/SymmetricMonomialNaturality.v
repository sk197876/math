(** Federer (1969), 1.10.5, p. 47, the monomial calculation for the induced
    inner product. Supporting naturality reduces a finite biorthogonal
    family in an arbitrary space to its coordinate space. The naturality
    identities themselves use neither an inner product nor characteristic
    zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedComponents AlgebraUP Hom BoundedHom ScalarCoefficients
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricLowPowers SymmetricMultiIndices SymmetricMonomials
  SymmetricDividedMonomials SymmetricForms SymmetricFormSum SymmetricFormDual
  SymmetricFormProduct SymmetricFormUnit SymmetricDualMonomialProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_divided_monomial_natural]: Federer 1.10.5,
    p. 47, supporting transport of the normalized monomials. The induced
    algebra map carries e^alpha/alpha! to f(e)^alpha/alpha!. *)
Lemma symmetric_divided_monomial_natural (K : fieldType) (V W : lmodType K)
    n (e : 'I_n -> V) (a : symmetric_multi_index n) (f : {linear V -> W}) :
  symmetric_algebra_map f (symmetric_divided_monomial e a) =
    symmetric_divided_monomial (f \o e) a.
Proof.
by rewrite /symmetric_divided_monomial linearZ symmetric_monomial_natural.
Qed.

(** Source for [symmetric_one_form_word_natural]: Federer 1.10.5,
    p. 47, supporting finite-dimensional reduction of the monomial
    pairing. Pullback of a product is the product of the pulled-back
    one-forms, including the empty product; this follows from 1.10.2. *)
Lemma symmetric_one_form_word_natural (K : fieldType) (V W : lmodType K)
    n (omega : 'I_n -> S_m W K^o 1) (f : {linear V -> W}) s :
  S_star_dual f (symmetric_one_form_word omega s) =
    symmetric_one_form_word (fun i => S_m_dual f (omega i)) s.
Proof.
elim: s=> [|i s ih].
- exact: S_star_dual_coefficient.
- change (S_star_dual f (symmetric_forms_product (scalar_bilinear K)
    (sform_include (omega i)) (symmetric_one_form_word omega s)) =
    symmetric_forms_product (scalar_bilinear K)
      (sform_include (S_m_dual f (omega i)))
      (symmetric_one_form_word (fun j => S_m_dual f (omega j)) s)).
  by rewrite S_star_dual_multiplicative S_star_dual_include ih.
Qed.

(** Source for [symmetric_one_form_monomial_natural]: Federer 1.10.5,
    p. 47, supporting transport of the dual monomials in the induced
    inner-product calculation. Pullback preserves each actual monomial
    product of one-forms, by the preceding word identity. *)
Lemma symmetric_one_form_monomial_natural (K : fieldType) (V W : lmodType K)
    n (omega : 'I_n -> S_m W K^o 1) (f : {linear V -> W}) a :
  S_star_dual f (symmetric_one_form_monomial omega a) =
    symmetric_one_form_monomial (fun i => S_m_dual f (omega i)) a.
Proof. exact: symmetric_one_form_word_natural. Qed.

(** Source for [symmetric_first_inclusion_natural]: Federer 1.10.5,
    p. 47, supporting transport of the polarity of each generator
    to a finite coordinate space. The first symmetric power of a linear
    map agrees with that map under the identifications of 1.9.1. *)
Lemma symmetric_first_inclusion_natural (K : fieldType) (U V : lmodType K)
    (f : {linear U -> V}) x :
  symmetric_power_map f 1 (symmetric_first_inclusion U x) =
    symmetric_first_inclusion V (f x).
Proof.
apply: val_inj.
change (symmetric_algebra_map f (grade (symmetric_grading U) 1 (symmetric_generator x)) =
  grade (symmetric_grading V) 1 (symmetric_generator (f x))).
by rewrite !symmetric_generator_homogeneous symmetric_algebra_mapE.
Qed.
