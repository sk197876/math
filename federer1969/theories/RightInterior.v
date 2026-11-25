(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import DualExterior.
From Federer Require Import InteriorUP RightInteriorHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1, the first displayed bilinear map and its
    characteristic condition. The right exterior map lowers Hom degree
    by p; the alternating-form isomorphism then gives eta interior phi. *)
Section RightInterior.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).
Variables p q : nat.
(** Source for [right_interior_degree]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma right_interior_degree (eta : exterior_power V p) (phi : Hom_m W G q) :
  hom_degree G (q-p) (right_interior_hom (component_val eta) phi).
Proof.
move=> n xi hn hxi; rewrite right_interior_homE.
apply: hom_m_degree (wedge_graded hxi (component_homogeneous eta)).
apply/eqP=> he; move: hn; rewrite -he addnK eqxx; by [].
Qed.
(** Source for [right_interior_homogeneous]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Definition
    or construction used to formalise this passage. *)
Definition right_interior_homogeneous (eta : exterior_power V p) (phi : A_m V W q) : Hom_m W G (q-p) :=
  @HomogeneousHom K E W G (q-p)
    (right_interior_hom (component_val eta) (form_homogeneous phi))
    (introT (asboolP _) (right_interior_degree eta (form_homogeneous phi))).
(** Source for [right_interior]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Definition
    or construction used to formalise this passage. *)
Definition right_interior (_ : (p <= q)%N) (eta : exterior_power V p) (phi : A_m V W q) : A_m V W (q-p) :=
  homogeneous_form (right_interior_homogeneous eta phi).
Variable hpq : (p <= q)%N.
(** Source for [right_interior_homogeneousE]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma right_interior_homogeneousE eta phi xi :
  form_homogeneous (right_interior hpq eta phi) xi =
    form_homogeneous phi (wedge xi (component_val eta)).
Proof. by rewrite /right_interior homogeneous_formK. Qed.
(** Source for [right_interior_characteristic]: Federer (1969), 1.5.1, p.
    21, right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_characteristic eta phi (xi : exterior_power V (q-p)) :
  pairing xi (right_interior hpq eta phi) =
    form_homogeneous phi (wedge (component_val xi) (component_val eta)).
Proof. exact: right_interior_homogeneousE. Qed.
(** Source for [right_interior_unique]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_unique eta phi (psi : A_m V W (q-p)) :
  (forall xi : exterior_power V (q-p), pairing xi psi =
    form_homogeneous phi (wedge (component_val xi) (component_val eta))) ->
  psi = right_interior hpq eta phi.
Proof. move=> h; apply: pairing_ext => xi; by rewrite h right_interior_characteristic. Qed.
(** Source for [right_interior_bilinear]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma right_interior_bilinear : bilinear (right_interior hpq).
Proof.
split.
- move=> phi c eta theta; apply: pairing_ext => xi.
  rewrite (proj2 (@pairing_bilinear K V W (q-p))).
  rewrite !right_interior_characteristic (linearP (@component_val K E G p))
    (proj2 (wedge_bilinear V)) linearP; by [].
- move=> eta c phi psi; apply: pairing_ext => xi.
  rewrite (proj2 (@pairing_bilinear K V W (q-p))).
  rewrite !right_interior_characteristic (linearP (@form_homogeneous K V W q))
    hom_m_addE hom_m_scaleE; by [].
Qed.
(** Federer 1.5.1: existence and the unique operation satisfying
    the previously stated characteristic condition. *)
(** Source for [right_interior_exists]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_exists : @is_right_interior K V W p q (right_interior hpq).
Proof. split; [exact: right_interior_bilinear | exact: right_interior_characteristic]. Qed.
(** Source for [right_interior_universal]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_universal : exists i : exterior_power V p -> A_m V W q -> A_m V W (q-p),
  is_right_interior i /\ forall j, is_right_interior j -> forall eta phi, j eta phi = i eta phi.
Proof.
exists (right_interior hpq); split; first exact: right_interior_exists.
move=> j [hj hc] eta phi; apply: right_interior_unique => xi; exact: hc.
Qed.
End RightInterior.

Declare Scope interior_scope.
Delimit Scope interior_scope with interior.
Notation "eta '⌟[' hpq ']' phi" := (right_interior hpq eta phi)
  (at level 40, hpq at level 0) : interior_scope.
