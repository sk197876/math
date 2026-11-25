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
From Federer Require Import AssociatedSubspace FiniteSpans SimpleWordIndependence
  AssociatedFiniteFamily.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first corollary: the associated space of a nonzero
    product is exactly the span of its factors. *)
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Local Notation xi := (e_lambda e (ord_tuple m)).
(** Source for [product_associated_generator]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma product_associated_generator i : FedererSimple.T xi (e i).
Proof.
change (wedge (component_val xi) (exterior_generator (e i)) = 0).
rewrite e_lambdaE.
have he : exterior_generator (e i) = exterior_word [:: e i].
  by rewrite exterior_word_cons exterior_word_nil wedge_unitr.
rewrite he exterior_word_cat.
change (exterior_word ([seq e j | j <- enum 'I_m] ++ [seq e j | j <- [:: i]]) = 0).
rewrite -map_cat.
apply: exterior_word_map_nonuniq.
by rewrite cats1 rcons_uniq mem_enum.
Qed.
(** Source for [product_associated_span]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma product_associated_span v : in_finite_span e v -> FedererSimple.T xi v.
Proof.
move=> [c ->].
apply: big_ind; first exact: subspace_zero.
- move=> x y; exact: subspace_add.
- move=> i _; exact: subspace_scale _ (product_associated_generator i).
Qed.
(** Source for [product_associated_space]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem product_associated_space : xi != 0 -> forall v,
  FedererSimple.T xi v <-> in_finite_span e v.
Proof.
move=> hx v; split; last exact: product_associated_span.
move=> hv; have [hs|hs] := pselect (in_finite_span e v); first exact: hs.
have hx' : exterior_word [seq e i | i <- enum 'I_m] != 0.
  apply/eqP=> h; apply: (elimT negP hx); apply/eqP; apply: val_inj.
  change (component_val xi = component_val (0 : exterior_power V m)).
  by rewrite e_lambdaE linear0.
have he := nonzero_word_independent hx'.
have hv' c : v != \sum_i c i *: e i.
  apply/eqP=> h; apply: hs; by exists c.
have hsno := finite_independent_snoc he hv'.
have ht i : FedererSimple.T xi (ordinal_snoc e v i).
  rewrite /ordinal_snoc; case: (unlift ord_max i) => [j|] //.
  exact: product_associated_generator.
have h := proj1 (@associated_finite_family K h2 V m m.+1 xi _ hsno ht hx).
by move: h; rewrite ltnn.
Qed.
End Products.
