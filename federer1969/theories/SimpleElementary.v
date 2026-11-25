(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, the simple-product convention and its elementary
    consequences used in the four corollaries. *)
Section Elementary.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [product_simple]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma product_simple m (e : 'I_m -> V) : simple (e_lambda e (ord_tuple m)).
Proof.
exists [tuple e i | i < m]; apply: val_inj.
change (component_val (e_lambda e (ord_tuple m)) = component_val (e_lambda idfun [tuple e i | i < m])).
by rewrite !e_lambdaE map_id.
Qed.
(** Source for [tuple_product]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tuple_product m (t : m.-tuple V) :
  e_lambda idfun t = e_lambda (tnth t) (ord_tuple m).
Proof.
apply: val_inj.
change (component_val (e_lambda idfun t) = component_val (e_lambda (tnth t) (ord_tuple m))).
rewrite !e_lambdaE map_id; congr (exterior_word _).
exact (congr1 (fun u : m.-tuple V => (val u : seq V)) (tuple_map_ord t)).
Qed.
(** Source for [simple_scale]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma simple_scale m (xi : exterior_power V m) c :
  (0 < m)%N -> simple xi -> simple (c *: xi).
Proof.
case: m xi => [|n] xi hm; first by [].
move=> [t ->]; case/tupleP: t => v t.
exists [tuple of (c *: v) :: t]; apply: val_inj.
change (component_val (c *: e_lambda idfun [tuple of v :: t]) =
  component_val (e_lambda idfun [tuple of (c *: v) :: t])).
rewrite linearZ !e_lambdaE !map_id /= !exterior_word_cons linearZ (bilZl (wedge_bilinear V)).
by rewrite map_id.
Qed.
(** Source for [associated_scale_nonzero]: Federer (1969), 1.6.1, p. 23,
    opening definition and displayed associated subspace T. In words: A
    simple m-vector is a product of m vectors; its associated subspace
    consists of vectors v for which xi wedge v is zero. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma associated_scale_nonzero m (xi : exterior_power V m) c : c != 0 ->
  forall v, FedererSimple.T (c *: xi) v <-> FedererSimple.T xi v.
Proof.
move=> hc v; change (wedge (component_val (c *: xi)) (exterior_generator v) = 0 <->
  wedge (component_val xi) (exterior_generator v) = 0).
rewrite linearZ (bilZl (wedge_bilinear V)).
split=> h; last by rewrite h scaler0.
have hz : c *: wedge (component_val xi) (exterior_generator v) == 0 by apply/eqP.
by move: hz; rewrite scaler_eq0 (negbTE hc) orFb => /eqP.
Qed.
End Elementary.
