(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: every exterior-algebra element
    involves a finite family of generators, also in infinite dimension. *)
Section FiniteSupport.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [exterior_finite_support]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem exterior_finite_support (x : exterior_space V) :
  exists s : seq V, forall f : {linear V -> V},
    (forall v, v \in s -> f v = v) -> exterior_algebra_map f x = x.
Proof.
elim/exterior_word_induction: x => [|x y [s hs] [t ht]|c x [s hs]|s].
- exists [::] => f hf; exact: linear0.
- exists (s++t) => f hf; rewrite linearD.
  have hx : exterior_algebra_map f x = x.
    apply: hs => v hv; apply: hf; by rewrite mem_cat hv.
  have hy : exterior_algebra_map f y = y.
    apply: ht => v hv; apply: hf; by rewrite mem_cat hv orbT.
  by rewrite hx hy.
- exists s => f hf; by rewrite linearZ (hs f hf).
- exists s => f hf; rewrite exterior_algebra_map_word.
  have hm : [seq f v | v <- s] = s.
    elim: s hf => [|v s ih] hf //=; rewrite (hf v (mem_head v s)).
    congr (_ :: _); apply: ih => w hw; apply: hf; by rewrite in_cons hw orbT.
  by rewrite hm.
Qed.
End FiniteSupport.
