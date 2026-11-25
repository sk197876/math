(** Federer (1969), 3.2.47, p. 282: the unique actual
    positive Gram–Schmidt recurrence, hidden behind its independent
    laws. The finite construction proves existence only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP FiniteIndependence
  PositiveGramSchmidtUP PositiveGramSchmidtExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type PositiveGramSchmidtSignature.
(** Source for [family]: the actual positively normalized recurrence
    in 3.2.47, p. 282, for an independent ordered finite input. *)
Parameter family:forall (R:rcfType) (V:lmodType R) B
  (hB:@is_inner_product R V B) n (u:'I_n->V),
  finite_independent u ->'I_n->V.
(** Source for [laws]: independent positive recurrence laws in
    3.2.47, p. 282, with nonzero residuals and every prefix span. *)
Parameter laws:forall (R:rcfType) (V:lmodType R) B
  (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u),
  is_positive_gram_schmidt hB u (@family R V B hB n u hu).
End PositiveGramSchmidtSignature.

Module PositiveGramSchmidt:PositiveGramSchmidtSignature.
(** Source for [family]: opaque selection from proved existence
    of the exact positive recurrence in 3.2.47, p. 282. *)
Definition family (R:rcfType) (V:lmodType R) B
    (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u):=
  projT1 (cid (@positive_gram_schmidt_exists R V B hB n u hu)).
(** Source for [laws]: the opaque family satisfies only the
    independent exact recurrence of 3.2.47, p. 282. *)
Lemma laws (R:rcfType) (V:lmodType R) B
    (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u):
  is_positive_gram_schmidt hB u (@family R V B hB n u hu).
Proof. exact:projT2 (cid (@positive_gram_schmidt_exists R V B hB n u hu)). Qed.
End PositiveGramSchmidt.
