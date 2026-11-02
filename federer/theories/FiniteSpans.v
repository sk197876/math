(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: a finite family is contained in the span of a finite
    independent family. This supplies the finite-dimensional space in
    the reduction; no basis for the ambient space is chosen. *)
Section FiniteSpans.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [in_finite_span]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition in_finite_span n (e : 'I_n -> V) (v : V) :=
  exists c : 'I_n -> K, v = \sum_i c i *: e i.
(** Source for [in_finite_span_zero]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma in_finite_span_zero n (e : 'I_n -> V) : in_finite_span e 0.
Proof. exists (fun _ => 0); symmetry; apply: big1 => i _; exact: scale0r. Qed.
(** Source for [in_finite_span_add]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma in_finite_span_add n (e : 'I_n -> V) x y :
  in_finite_span e x -> in_finite_span e y -> in_finite_span e (x+y).
Proof.
move=> [c ->] [d ->]; exists (fun i => c i+d i).
rewrite -big_split; apply: eq_bigr => i _; symmetry; exact: scalerDl.
Qed.
(** Source for [in_finite_span_scale]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma in_finite_span_scale n (e : 'I_n -> V) a x :
  in_finite_span e x -> in_finite_span e (a *: x).
Proof.
move=> [c ->]; exists (fun i => a*c i).
rewrite scaler_sumr; apply: eq_bigr => i _; exact: scalerA.
Qed.
(** Source for [in_finite_span_snoc]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma in_finite_span_snoc n (e : 'I_n -> V) v x :
  in_finite_span e x -> in_finite_span (ordinal_snoc e v) x.
Proof.
move=> [c ->]; exists (ordinal_snoc c 0).
rewrite big_ord_recr !ordinal_snoc_last scale0r.
change ((\sum_i c i *: e i) =
  (\sum_(i < n) ordinal_snoc c 0 (widen_ord (leqnSn n) i) *:
    ordinal_snoc e v (widen_ord (leqnSn n) i)) + 0).
rewrite addr0; apply: eq_bigr => i _; by rewrite !ordinal_snoc_before.
Qed.
(** Source for [in_finite_span_last]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma in_finite_span_last n (e : 'I_n -> V) v :
  in_finite_span (ordinal_snoc e v) v.
Proof.
exists (ordinal_snoc (fun _ : 'I_n => (0 : K)) 1).
rewrite big_ord_recr !ordinal_snoc_last scale1r.
have hz : (\sum_(i < n) ordinal_snoc (fun _ : 'I_n => (0 : K)) 1 (widen_ord (leqnSn n) i) *:
  ordinal_snoc e v (widen_ord (leqnSn n) i)) = 0.
  apply: big1 => i _; by rewrite ordinal_snoc_before scale0r.
rewrite hz; change (v = (0 : V) + v); by rewrite add0r.
Qed.
(** Source for [finite_independent_span]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem finite_independent_span (s : seq V) :
  exists n (e : 'I_n -> V), finite_independent e /\
    (forall v, v \in s -> in_finite_span e v).
Proof.
elim: s => [|v s [n [e [he hs]]]].
- exists 0%N, (fun _ : 'I_0 => (0 : V)); split.
  + move=> c hc i; by have := ltn_ord i; rewrite ltn0.
  + by move=> v; rewrite in_nil.
- have [hv|hv] := pselect (in_finite_span e v).
  + exists n, e; split=> // w; rewrite in_cons => /orP [/eqP ->|hw] //; exact: hs.
  + have hv' c : v != \sum_i c i *: e i.
      apply/eqP=> h; apply: hv; by exists c.
    exists n.+1, (ordinal_snoc e v); split; first exact: finite_independent_snoc he hv'.
    move=> w; rewrite in_cons => /orP [/eqP ->|hw]; first exact: in_finite_span_last.
    exact: in_finite_span_snoc (hs w hw).
Qed.
End FiniteSpans.
