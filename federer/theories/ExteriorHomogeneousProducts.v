(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: exterior products and the harmless changes of
    degree index required to write q-p+p=q in the characteristic
    conditions. These are the same exterior products as in 1.3.1. *)
Section Products.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [exterior_product]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition exterior_product p q (xi : exterior_power V p) (eta : exterior_power V q) : exterior_power V (p+q) :=
  @Component K (exterior_space V) (exterior_grading V) (p+q)
    (wedge (component_val xi) (component_val eta))
    (introT eqP (wedge_graded (component_homogeneous xi) (component_homogeneous eta))).
(** Source for [exterior_productE]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_productE p q (xi : exterior_power V p) (eta : exterior_power V q) :
  component_val (exterior_product xi eta) = wedge (component_val xi) (component_val eta).
Proof. by []. Qed.
(** Source for [exterior_product_bilinear]: Federer (1969), 1.5.1, p. 21,
    opening two bilinear maps and characteristic pairing conditions. In
    words: Right interior multiplication is characterised by adjoining the
    vector on the right inside the pairing; left interior multiplication is
    characterised by multiplying the covector on the left. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma exterior_product_bilinear p q : bilinear (@exterior_product p q).
Proof.
split.
- move=> eta c xi zeta; apply: val_inj.
  change (wedge (component_val (c *: xi+zeta)) (component_val eta) =
    component_val (c *: exterior_product xi eta + exterior_product zeta eta)).
  by rewrite !linearP ?exterior_productE ?(proj1 (wedge_bilinear V)).
- move=> xi c eta zeta; apply: val_inj.
  change (wedge (component_val xi) (component_val (c *: eta+zeta)) =
    component_val (c *: exterior_product xi eta + exterior_product xi zeta)).
  by rewrite !linearP ?exterior_productE ?(proj2 (wedge_bilinear V)).
Qed.
(** Source for [exterior_reindex]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition exterior_reindex m n (h : m=n) (xi : exterior_power V m) : exterior_power V n :=
  match h in _ = n return exterior_power V n with erefl => xi end.
(** Source for [exterior_reindexE]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_reindexE m n (h : m=n) (xi : exterior_power V m) :
  component_val (exterior_reindex h xi) = component_val xi.
Proof. by case: n / h. Qed.
(** Source for [exterior_reindex_linear]: Federer (1969), 1.5.1, p. 21,
    opening two bilinear maps and characteristic pairing conditions. In
    words: Right interior multiplication is characterised by adjoining the
    vector on the right inside the pairing; left interior multiplication is
    characterised by multiplying the covector on the left. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma exterior_reindex_linear m n (h : m=n) : linear (@exterior_reindex m n h).
Proof. by case: n / h => c x y. Qed.
HB.instance Definition _ m n (h : m=n) := GRing.isLinear.Build K (exterior_power V m)
  (exterior_power V n) *:%R (exterior_reindex h) (exterior_reindex_linear h).
Variable W : lmodType K.
(** Source for [form_reindex]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Definition or construction used
    to formalise this passage. *)
Definition form_reindex m n (h : m=n) (phi : A_m V W m) : A_m V W n :=
  match h in _ = n return A_m V W n with erefl => phi end.
(** Source for [form_reindexE]: Federer (1969), 1.5.1, p. 21, opening two
    bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_reindexE m n (h : m=n) (phi : A_m V W m) x :
  form_homogeneous (form_reindex h phi) x = form_homogeneous phi x.
Proof. by case: n / h. Qed.
(** Source for [form_reindex_linear]: Federer (1969), 1.5.1, p. 21, opening
    two bilinear maps and characteristic pairing conditions. In words: Right
    interior multiplication is characterised by adjoining the vector on the
    right inside the pairing; left interior multiplication is characterised
    by multiplying the covector on the left. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_reindex_linear m n (h : m=n) : linear (@form_reindex m n h).
Proof. by case: n / h => c x y. Qed.
HB.instance Definition _ m n (h : m=n) := GRing.isLinear.Build K (A_m V W m)
  (A_m V W n) *:%R (form_reindex h) (form_reindex_linear h).
End Products.
