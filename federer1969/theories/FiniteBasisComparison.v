(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import InteriorDecomposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: independence of the prescribed basis and invariance
    of its size. These statements use coordinate functionals and the
    abstract dimension, without a matrix representation. *)
Section Basis.
Variable K : fieldType.
Variable V : lmodType K.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [finite_basis_independent]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem finite_basis_independent : finite_independent e.
Proof.
apply: (@finite_independent_separating K I V e
  (fun i => hom_as_linear (dual_basis he i))) => i j.
change (dual_basis he i (e j) = if i == j then 1 else 0).
by rewrite dual_basisE eq_sym.
Qed.
End Basis.

(** Source for [finite_independent_dimension]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_independent_dimension (K : fieldType) (V : vectType K) k (e : 'I_k -> V) :
  finite_independent e -> (k <= dim V)%N.
Proof.
move=> he; pose t : k.-tuple V := [tuple e i | i < k].
have ht (i : 'I_k) : t`_i = e i := nth_mktuple e (0 : V) i.
have hf : free t.
  apply/freeP=> c hc; apply: he.
  have hs : (\sum_i c i *: t`_i) = \sum_i c i *: e i.
    apply: eq_bigr => i _; by rewrite ht.
  by rewrite -hs.
have hd : \dim <<t>> = k by move/eqP: hf; rewrite /free size_tuple.
have h := @dimvS K V <<t>> {:V} (subvf _).
by rewrite hd dimvf in h.
Qed.

(** Source for [finite_basis_size]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Theorem finite_basis_size (K : fieldType) (V : lmodType K) k l
  (e : 'I_k -> V) (f : 'I_l -> V) : is_basis e -> is_basis f -> k = l.
Proof.
move=> he hf; apply/eqP; rewrite eqn_leq; apply/andP; split.
- have h := @finite_independent_dimension K (finite_basis_vect hf) k e (finite_basis_independent he).
  by rewrite finite_basis_dimension card_ord in h.
- have h := @finite_independent_dimension K (finite_basis_vect he) l f (finite_basis_independent hf).
  by rewrite finite_basis_dimension card_ord in h.
Qed.
