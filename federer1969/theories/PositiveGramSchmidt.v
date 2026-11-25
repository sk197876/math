(** Federer (1969), 3.2.47, p. 282: public positive
    Gram–Schmidt recurrence. Smoothness arguments use these exact
    laws and uniqueness, never a private recursive implementation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP FiniteIndependence PositiveGramSchmidtUP
  PositiveGramSchmidtUniqueness PositiveGramSchmidtSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [positive_gram_schmidt_family]: the exact family
    prescribed by the normalized recurrence in 3.2.47, p. 282. *)
Definition positive_gram_schmidt_family (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u):=
  @PositiveGramSchmidt.family R V B hB n u hu.

(** Source for [positive_gram_schmidt_laws]: the full independent
    laws of the positive recurrence in 3.2.47, p. 282. *)
Theorem positive_gram_schmidt_laws (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u):
  is_positive_gram_schmidt hB u (positive_gram_schmidt_family hB hu).
Proof. exact:PositiveGramSchmidt.laws. Qed.

(** Source for [positive_gram_schmidt_input_proof_independent]:
    the recurrence in 3.2.47, p. 282, depends on the actual
    ordered input, rather than on its independence proof. *)
Lemma positive_gram_schmidt_input_proof_independent (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V) (h1 h2:finite_independent u):
  positive_gram_schmidt_family hB h1=1 positive_gram_schmidt_family hB h2.
Proof. exact:positive_gram_schmidt_unique (positive_gram_schmidt_laws hB h1)
  (positive_gram_schmidt_laws hB h2). Qed.
