(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for the double sum over Sh(p,q) in Federer 1.3.3. *)
(** Source for [sum_subtype]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma sum_subtype (Z : zmodType) (I : finType) (P : pred I) (f : I -> Z) :
  \sum_(i | P i) f i = \sum_(i : {i : I | P i}) f (val i).
Proof.
rewrite (reindex_omap (fun i : {i : I | P i} => (val i : I))
  (insub : I -> option {i : I | P i})).
- apply: eq_bigl => i; by rewrite valP valK eqxx.
- move=> i hi; by rewrite (insubT P hi) /=.
Qed.
