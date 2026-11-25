(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, dimension qualification: independent pairs possess
    dual covectors on the whole space, also in infinite dimension. *)
Section IndependentDual.
Variable K : fieldType.
Variable V : lmodType K.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : finite_independent e.
(** Source for [independent_dual]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Definition or
    construction used to formalise this passage. The zero-dimensional
    examples are local counterexamples to the unrestricted printed
    exception, not examples stated in Federer. *)
Definition independent_dual i : Hom V K^o := hom_of_linear
  (extension_along (finite_synthesis_injective he)
    (GRing.Linear.clone _ _ _ _ (free_eval i) _)).
(** Source for [independent_dualE]: Federer (1969), 1.4.5, p. 20, opening
    sentence and its parenthesised exception. In words: The ordinary tensor
    product of two exterior algebras is asserted to be neither commutative
    nor anticommutative apart from the printed exception. Supporting lemma
    for this passage; not separately stated in the book. The
    zero-dimensional examples are local counterexamples to the unrestricted
    printed exception, not examples stated in Federer. *)
Lemma independent_dualE i j : independent_dual i (e j) = if i == j then 1 else 0.
Proof.
rewrite /independent_dual hom_of_linearE -(@basis_synthesisE K (Choice.clone I _) V e j)
  extension_alongE.
change (delta K j i = if i == j then 1 else 0).
exact: deltaE.
Qed.
End IndependentDual.
