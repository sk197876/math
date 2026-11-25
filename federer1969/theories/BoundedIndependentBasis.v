(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InteriorDecomposition.
From Federer Require Import FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, the meaning of dim T<=m in an initially arbitrary
    ambient space: a bound on all finite independent families produces
    a finite basis. The proof takes a family of maximum possible length. *)
Section Bounded.
Variable K : fieldType.
Variable U : lmodType K.
Variable m : nat.
Hypothesis bound : forall k (e : 'I_k -> U), finite_independent e -> (k <= m)%N.
(** Source for [bounded_independent_basis]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem bounded_independent_basis :
  exists k (e : 'I_k -> U), is_basis e /\ (k <= m)%N.
Proof.
pose P k := `[< exists e : 'I_k -> U, finite_independent e >].
have exP : exists k, P k.
  exists 0%N; apply/asboolP; exists (fun _ : 'I_0 => (0 : U)).
  move=> c hc i; by have := ltn_ord i; rewrite ltn0.
have ubP k : P k -> (k <= m)%N.
  move/asboolP=> [e he]; exact: bound he.
have [k /asboolP [e he] hk] := @ex_maxnP P m exP ubP.
have hs v : in_finite_span e v.
  have [hv|hv] := pselect (in_finite_span e v); first exact: hv.
  have hv' c : v != \sum_i c i *: e i.
    apply/eqP=> h; apply: hv; by exists c.
  have he' := finite_independent_snoc he hv'.
  have hp : P k.+1 by apply/asboolP; exists (ordinal_snoc e v).
  by have := hk k.+1 hp; rewrite ltnn.
exists k, e; split; last exact: bound he.
exact: finite_basis_criterion he hs.
Qed.
End Bounded.
