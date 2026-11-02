(** Federer (1969), 1.10.5, p. 47: the algebra extension of the polarity
    carries monomials to products of their dual one-forms. These are
    consequences of the sealed algebra-map laws, independent of a choice of
    basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Hom BoundedHom GradedComponents
  InnerProductUP InnerSymmetricPolarity InnerSymmetric
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricMonomials
  SymmetricForms SymmetricFormSum SymmetricPairing SymmetricFormUnit
  SymmetricFormProduct ScalarCoefficients SymmetricDualMonomialProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Monomials.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [inner_symmetric_word]: Federer 1.10.5,
    p. 47, supporting multiplication calculation for the first
    displayed monomial formula. The image of a finite product of
    generators is the actual symmetric product of their polarities. *)
Lemma inner_symmetric_word s :
  inner_symmetric_extension hB (symmetric_word [seq e i | i <- s]) =
    symmetric_one_form_word (fun i => inner_symmetric_polarity hB (e i)) s.
Proof.
elim: s=> [|i s ih].
- rewrite /= symmetric_word_nil.
  exact: (@algebra_map_one R (symmetric_algebra V)
    (symmetric_forms_unital_algebra V (scalar_algebra R)) (inner_symmetric_extension hB)).
- rewrite /= symmetric_word_cons algebra_map_mul inner_symmetric_generator ih.
  by [].
Qed.

(** Source for [inner_symmetric_monomial]: Federer 1.10.5,
    p. 47, the polarity extension maps e^alpha to the
    monomial in the polarities of e_i. This is the algebraic part
    of the normalized-orthonormal-monomial assertion. *)
Lemma inner_symmetric_monomial (a : symmetric_multi_index n) :
  inner_symmetric_extension hB (symmetric_monomial e a) =
    symmetric_one_form_monomial (fun i => inner_symmetric_polarity hB (e i)) a.
Proof.
rewrite /symmetric_monomial /symmetric_one_form_monomial -inner_symmetric_word.
congr (inner_symmetric_extension hB (symmetric_word _)).
by rewrite symmetric_monomial_word_map.
Qed.

(** Source for [symmetric_inner_formE]: Federer 1.10.5,
    p. 47, the inner-product definition by gamma. This
    supporting evaluation identity expresses the degree-m pairing
    using the full sealed algebra extension. *)
Lemma symmetric_inner_formE m (x y : symmetric_power V m) :
  symmetric_inner_form hB x y =
    inner_symmetric_extension hB (component_val y) (component_val x).
Proof.
rewrite /symmetric_inner_form -inner_symmetric_form_include.
by [].
Qed.
End Monomials.
