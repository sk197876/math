(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier FiniteSpans FiniteSpanSpace ExteriorSubspaceReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: choose a finite-dimensional subspace carrying xi
    and containing any prescribed finite family. This proves the finite
    reduction used for T and its finite independent families. *)
Section Reduction.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
(** Source for [exterior_finite_dimensional_reduction]: Federer (1969),
    1.6.1, p. 23, dimension bound, factorisation assertion, and
    finite-dimensional reduction. In words: For a nonzero m-vector the
    associated space has dimension k<=m; the product of any basis of that
    space factors from the vector, leaving degree m-k. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem exterior_finite_dimensional_reduction (s : seq V) :
  exists n (e : 'I_n -> V) (he : finite_independent e),
    (forall v, v \in s -> finite_span_subspace e v) /\
    exists eta : exterior_power (finite_span_vect he) m,
      exterior_power_map (subspace_inclusion (finite_span_subspace e)) m eta = xi.
Proof.
have [t ht] := exterior_subspace_finite_support xi.
have [n [e [he hs]]] := finite_independent_span (t++s).
exists n, e, he; split.
- move=> v hv; apply: hs; by rewrite mem_cat hv orbT.
- apply: ht => v hv; apply: hs; by rewrite mem_cat hv.
Qed.
End Reduction.
