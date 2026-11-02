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

(** Federer 1.6.1: extend the given e_1,...,e_k to a finite basis of V,
    preserving each of these vectors and its position. The construction
    successively adjoins only vectors outside the preceding span. *)
Section Extension.
Variable K : fieldType.
Variable V : lmodType K.
Variable k : nat.
Variable e : 'I_k -> V.
Hypothesis he : finite_independent e.
(** Source for [finite_independent_extend]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem finite_independent_extend (s : seq V) :
  exists n (hkn : (k <= n)%N) (f : 'I_n -> V),
    finite_independent f /\
    (forall i, f (widen_ord hkn i) = e i) /\
    (forall v, v \in s -> in_finite_span f v).
Proof.
elim: s => [|v s [n [hkn [f [hf [hfe hs]]]]]].
- exists k, (leqnn k), e; split=> //; split.
  + move=> i; congr (e _); exact: val_inj.
  + by move=> v; rewrite in_nil.
- have [hv|hv] := pselect (in_finite_span f v).
  + exists n, hkn, f; split=> //; split=> // w.
    rewrite in_cons => /orP [/eqP ->|hw] //; exact: hs.
  + have hv' c : v != \sum_i c i *: f i.
      apply/eqP=> h; apply: hv; by exists c.
    pose hkn' := leq_trans hkn (leqnSn n).
    exists n.+1, hkn', (ordinal_snoc f v); split.
    * exact: finite_independent_snoc hf hv'.
    * split.
      -- move=> i.
         have hi : widen_ord hkn' i = widen_ord (leqnSn n) (widen_ord hkn i) by apply: val_inj.
         by rewrite hi ordinal_snoc_before hfe.
      -- move=> w; rewrite in_cons => /orP [/eqP ->|hw]; first exact: in_finite_span_last.
         exact: in_finite_span_snoc (hs w hw).
Qed.
Variable l : nat.
Variable b : 'I_l -> V.
Hypothesis hb : is_basis b.
(** Source for [finite_basis_extension]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem finite_basis_extension :
  exists n (hkn : (k <= n)%N) (f : 'I_n -> V),
    is_basis f /\ forall i, f (widen_ord hkn i) = e i.
Proof.
have [n [hkn [f [hf [hfe hs]]]]] := finite_independent_extend [seq b i | i <- enum 'I_l].
exists n, hkn, f; split=> //; apply: finite_basis_criterion hf _.
apply: (basis_induction hb) => [|x y hx hy|c x hx|i].
- exact: in_finite_span_zero.
- exact: in_finite_span_add hx hy.
- exact (@in_finite_span_scale K V n f c x hx).
- apply: hs; apply/mapP; exists i => //; exact: mem_enum.
Qed.
End Extension.
