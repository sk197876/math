(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import InteriorUP PairingSeparation ScalarTensorContraction
  ExteriorHomogeneousProducts LeftInteriorHom LeftInteriorDegree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1, the second bilinear operation and its characteristic
    condition. It is constructed by the displayed diagonal composite,
    and uniquely characterised by the pairing. *)
Section LeftInterior.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables p q : nat.
(** Source for [left_interior]: Federer (1969), 1.5.1, p. 22, diagonal-map
    composite and commutative diagram. In words: Apply the diagonal,
    evaluate the first factor against the homogeneous covector, then use
    scalar multiplication on the remaining factor; the diagram proves the
    characteristic pairing identity. Definition or construction used to
    formalise this passage. *)
Definition left_interior (_ : (p <= q)%N) (zeta : exterior_power V q) (a : A_m V K^o p) :
  exterior_power V (q-p) :=
  @Component K (exterior_space V) (exterior_grading V) (q-p)
    (left_interior_hom h2 (component_val zeta) (form_homogeneous a))
    (introT eqP (left_interior_degree h2 zeta a)).
Variable hpq : (p <= q)%N.
(** Source for [left_interiorE]: Federer (1969), 1.5.1, p. 22, diagonal-map
    composite and commutative diagram. In words: Apply the diagonal,
    evaluate the first factor against the homogeneous covector, then use
    scalar multiplication on the remaining factor; the diagram proves the
    characteristic pairing identity. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma left_interiorE zeta a : component_val (left_interior hpq zeta a) =
  left_interior_hom h2 (component_val zeta) (form_homogeneous a).
Proof. by []. Qed.
(** Source for [left_interior_characteristic]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_characteristic zeta a (b : A_m V K^o (q-p)) :
  pairing (left_interior hpq zeta a) b =
    pairing zeta (form_reindex (subnKC hpq) (form_wedge h2 (scalar_bilinear K) a b)).
Proof.
change (form_homogeneous b (component_val (left_interior hpq zeta a)) =
  form_homogeneous (form_reindex (subnKC hpq) (form_wedge h2 (scalar_bilinear K) a b)) (component_val zeta)).
rewrite left_interiorE form_reindexE /form_wedge homogeneous_formK.
exact: left_interior_diagram.
Qed.
(** Source for [left_interior_unique]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_unique zeta a (xi : exterior_power V (q-p)) :
  (forall b : A_m V K^o (q-p), pairing xi b =
    pairing zeta (form_reindex (subnKC hpq) (form_wedge h2 (scalar_bilinear K) a b))) ->
  xi = left_interior hpq zeta a.
Proof.
move=> h; apply: pairing_vectors_separate => b.
by rewrite h left_interior_characteristic.
Qed.
(** Source for [left_interior_bilinear]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma left_interior_bilinear : bilinear (left_interior hpq).
Proof.
split.
- move=> a c x y; apply: val_inj.
  change (left_interior_hom h2 (component_val (c *: x+y)) (form_homogeneous a) =
    component_val (c *: left_interior hpq x a + left_interior hpq y a)).
  by rewrite !linearP ?left_interiorE (proj1 (left_interior_hom_bilinear h2 V)).
- move=> x c a b; apply: val_inj.
  change (left_interior_hom h2 (component_val x) (form_homogeneous (c *: a+b)) =
    component_val (c *: left_interior hpq x a + left_interior hpq x b)).
  by rewrite !linearP ?left_interiorE (proj2 (left_interior_hom_bilinear h2 V)).
Qed.
(** Federer 1.5.1: existence and uniqueness of the second operation. *)
(** Source for [left_interior_exists]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_exists : @is_left_interior K V p q h2 hpq (left_interior hpq).
Proof. split; [exact: left_interior_bilinear | exact: left_interior_characteristic]. Qed.
(** Source for [left_interior_universal]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_universal : exists i : exterior_power V q -> A_m V K^o p -> exterior_power V (q-p),
  is_left_interior h2 hpq i /\ forall j, is_left_interior h2 hpq j -> forall zeta a, j zeta a = i zeta a.
Proof.
exists (left_interior hpq); split; first exact: left_interior_exists.
move=> j [hj hc] zeta a; apply: left_interior_unique => b; exact: hc.
Qed.
End LeftInterior.

Declare Scope left_interior_scope.
Delimit Scope left_interior_scope with left_interior.
Notation "zeta '⌞[' h2 ',' hpq ']' a" := (left_interior h2 hpq zeta a)
  (at level 40, h2 at level 0, hpq at level 0) : left_interior_scope.
