(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2: the product of any ordered basis of an
    m-dimensional subspace is a nonzero simple m-vector whose
    associated subspace is that very subspace. This includes m=0. *)
Section Product.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable S : subspace V.
Variable m : nat.
Variable e : 'I_m -> subspace_space S.
Hypothesis he : is_basis e.
Local Notation ev := (fun i => subspace_val (e i)).
(** Source for [subspace_basis_product]: Federer (1969), 1.6.2, p. 24, first
    sentence, surjectivity of the association. In words: Every m-dimensional
    subspace is the associated subspace of a nonzero simple m-vector,
    obtained by taking the exterior product of a basis. Definition or
    construction used to formalise this passage. *)
Definition subspace_basis_product := e_lambda ev (ord_tuple m).
(** Source for [subspace_basis_product_nonzero]: Federer (1969), 1.6.2, p.
    24, first sentence, surjectivity of the association. In words: Every
    m-dimensional subspace is the associated subspace of a nonzero simple
    m-vector, obtained by taking the exterior product of a basis. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma subspace_basis_product_nonzero : subspace_basis_product != 0.
Proof.
apply: (@independent_product_nonzero K h2 V m ev).
exact: finite_independent_map (@subspace_val_injective K V S) (finite_basis_independent he).
Qed.
(** Source for [subspace_basis_product_simple]: Federer (1969), 1.6.2, p.
    24, first sentence, surjectivity of the association. In words: Every
    m-dimensional subspace is the associated subspace of a nonzero simple
    m-vector, obtained by taking the exterior product of a basis. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma subspace_basis_product_simple : simple subspace_basis_product.
Proof. exact: product_simple. Qed.
(** Source for [subspace_basis_span]: Federer (1969), 1.6.2, p. 24, first
    sentence, surjectivity of the association. In words: Every m-dimensional
    subspace is the associated subspace of a nonzero simple m-vector,
    obtained by taking the exterior product of a basis. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma subspace_basis_span v : in_finite_span ev v <-> S v.
Proof.
split.
- move=> [c ->]; apply: big_ind; first exact: subspace_zero.
  + move=> x y; exact: subspace_add.
  + move=> i _; exact: subspace_scale _ (subspace_valP (e i)).
- move=> hv; pose z := subspace_lift hv.
  pose c i := basis_coordinates he z i.
  have heq : z = \sum_i c i *: e i.
    by rewrite /c -basis_synthesis_finiteE basis_coordinatesK.
  exists c; have h := congr1 (@subspace_val K V S) heq.
  rewrite linear_sum in h; apply: eq_trans h _.
  apply: eq_bigr => i _; exact: linearZ.
Qed.
(** Source for [subspace_basis_product_associated]: Federer (1969), 1.6.2,
    p. 24, first sentence, surjectivity of the association. In words: Every
    m-dimensional subspace is the associated subspace of a nonzero simple
    m-vector, obtained by taking the exterior product of a basis. Supporting
    lemma for this passage; not separately stated in the book. *)
Theorem subspace_basis_product_associated v :
  FedererSimple.T subspace_basis_product v <-> S v.
Proof.
rewrite (@product_associated_space K h2 V m ev subspace_basis_product_nonzero v).
exact: subspace_basis_span.
Qed.
End Product.
