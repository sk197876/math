(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SubspaceCarrier SubspaceFamilies
  SimpleWordIndependence SimpleProducts SimpleElementary FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first corollary: the factors of a nonzero simple
    m-vector, regarded in T, form a basis of T. *)
Section Basis.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Local Notation xi := (e_lambda e (ord_tuple m)).
Local Notation T := (FedererSimple.T xi).
(** Source for [product_basis]: Federer (1969), 1.6.1, p. 24, first of the
    four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Definition or
    construction used to formalise this passage. For the literal
    empty-product definition the reverse implication requires m>0. *)
Definition product_basis : 'I_m -> subspace_space T :=
  subspace_family (product_associated_generator e).
(** Source for [product_basisE]: Federer (1969), 1.6.1, p. 24, first of the
    four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Supporting lemma for
    this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Lemma product_basisE i : subspace_val (product_basis i) = e i.
Proof. by []. Qed.
(** Source for [product_basisP]: Federer (1969), 1.6.1, p. 24, first of the
    four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Supporting lemma for
    this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Theorem product_basisP : xi != 0 -> is_basis product_basis.
Proof.
move=> hx.
have hw : exterior_word [seq e i | i <- enum 'I_m] != 0.
  apply/eqP=> h; apply: (elimT negP hx); apply/eqP; apply: val_inj.
  change (component_val xi = component_val (0 : exterior_power V m)).
  by rewrite e_lambdaE linear0.
have he := nonzero_word_independent hw.
apply: finite_basis_criterion (subspace_family_independent he) _ => v.
have [c hc] := proj1 (@product_associated_space K h2 V m e hx (subspace_val v)) (subspace_valP v).
exists c; apply: val_inj; change (subspace_val v = subspace_val (\sum_i c i *: product_basis i)).
rewrite linear_sum hc; apply: eq_bigr => i _; by rewrite linearZ.
Qed.
End Basis.
