(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import FiniteSpans ConcatenatedFamilies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, third corollary: the concatenation of two independent
    families is independent precisely when their spans intersect at zero. *)
Section Independence.
Variable K : fieldType.
Variable V : lmodType K.
Variables m n : nat.
Variables (e : 'I_m -> V) (f : 'I_n -> V).
(** Source for [independent_concatenation_disjoint]: Federer (1969), 1.6.1,
    p. 24, third corollary. In words: The wedge of two nonzero simple
    vectors is nonzero exactly when its associated subspace is the direct
    sum of their associated subspaces. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma independent_concatenation_disjoint : finite_independent (concatenate_family e f) ->
  forall x, in_finite_span e x -> in_finite_span f x -> x=0.
Proof.
move=> hi x [a ha] [b hb].
pose c := concatenate_family a (fun i => -b i).
have hc : (\sum_i c i *: concatenate_family e f i) = 0.
  rewrite /c concatenate_family_combination.
  have hn : (\sum_i -b i *: f i) = -\sum_i b i *: f i.
    by rewrite -sumrN; apply: eq_bigr => i _; rewrite scaleNr.
  by rewrite hn -ha -hb subrr.
have hzero i : a i = 0.
  have h := hi c hc (lshift n i); by rewrite /c concatenate_family_l in h.
rewrite ha; apply: big1 => i _; by rewrite hzero scale0r.
Qed.
Hypotheses (he : finite_independent e) (hf : finite_independent f).
(** Source for [disjoint_concatenation_independent]: Federer (1969), 1.6.1,
    p. 24, third corollary. In words: The wedge of two nonzero simple
    vectors is nonzero exactly when its associated subspace is the direct
    sum of their associated subspaces. Supporting lemma for this passage;
    not separately stated in the book. *)
Theorem disjoint_concatenation_independent :
  (forall x, in_finite_span e x -> in_finite_span f x -> x=0) ->
  finite_independent (concatenate_family e f).
Proof.
move=> hd c hc.
pose x := \sum_i c (lshift n i) *: e i.
pose y := \sum_i c (rshift m i) *: f i.
have hxy : x+y=0 by rewrite /x /y -concatenate_family_sum.
have hxe : in_finite_span e x by exists (fun i => c (lshift n i)).
have hyf : in_finite_span f y by exists (fun i => c (rshift m i)).
have heq : x = -y.
  apply: (addIr y); by rewrite addNr hxy.
have hxf : in_finite_span f x.
  rewrite heq; have h := @in_finite_span_scale K V n f (-1) y hyf.
  by rewrite scaleN1r in h.
have hx := hd x hxe hxf.
have hy : y=0 by move: hxy; rewrite hx add0r.
have hel := @he (fun i => c (lshift n i)) hx.
have hfr := @hf (fun i => c (rshift m i)) hy.
move=> i; case: (split_ordP i) => [j ->|j ->]; [exact: hel|exact: hfr].
Qed.
End Independence.
