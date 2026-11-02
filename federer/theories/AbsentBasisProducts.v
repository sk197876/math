(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SingleIndexContraction AssociatedSubspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, the basis expansion: multiplication by e_i kills
    xi only if xi_lambda=0 for every lambda omitting i. *)
Section Coordinates.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [basis_normalisation]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_normalisation i : one_hom (omega i) (e i) = 1.
Proof. by rewrite one_homE hdual eqxx. Qed.
(** Source for [associated_coordinate_zero]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem associated_coordinate_zero (xi : exterior_power V m) i (lambda : Lambda n m) :
  FedererSimple.T xi (e i) -> i \notin Lambda_set lambda ->
  xi_lambda h2 omega xi lambda = 0.
Proof.
move=> hx hi.
exact (@annihilator_pairing_zero K h2 V (e i) (omega i) (basis_normalisation i)
  (form_homogeneous (omega_lambda h2 omega lambda))
  (@basis_covector_absent K h2 V n e omega he hdual m lambda i hi)
  (component_val xi) hx).
Qed.

(** Federer 1.6.1: the products e_lambda wedge e_i with i absent are
    linearly independent, as asserted in the proof. The dual functionals
    are evaluation against omega_lambda wedge omega_i. *)
Variable i : 'I_n.
Local Notation I := {lambda : Lambda n m | i \notin Lambda_set lambda}.
Local Notation E := (exterior_space V).
(** Source for [absent_basis_product]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Definition or construction used to
    formalise this passage. *)
Definition absent_basis_product (lambda : I) : E :=
  wedge (component_val (e_lambda e (val (val lambda)))) (exterior_generator (e i)).
(** Source for [absent_basis_dual]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Definition or construction used to
    formalise this passage. *)
Definition absent_basis_dual (lambda : I) : Hom E K^o :=
  convolution (scalar_bilinear K) (Psi h2 V)
    (form_homogeneous (omega_lambda h2 omega (val lambda))) (form_homogeneous (omega i)).
(** Source for [absent_basis_biorthogonal]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma absent_basis_biorthogonal (lambda mu : I) :
  absent_basis_dual lambda (absent_basis_product mu) = if lambda == mu then 1 else 0.
Proof.
rewrite /absent_basis_dual /absent_basis_product right_covector_product basis_normalisation mul1r.
have hz := @basis_covector_absent K h2 V n e omega he hdual m (val lambda) i (valP lambda).
rewrite hz (bil0l (@convolution_bilinear K E K^o _ (scalar_bilinear K) (Psi h2 V))) hom_zeroE subr0.
change (pairing (e_lambda e (val (val mu))) (omega_lambda h2 omega (val lambda)) =
  if lambda == mu then 1 else 0).
by rewrite (pairing_e_omega h2 hdual) val_eqE.
Qed.
(** Source for [absent_basis_products_independent]: Federer (1969), 1.6.1,
    p. 23, last paragraph, basis extension and the Grassmann-coordinate
    argument. In words: Extend a basis of the associated space to an ambient
    finite basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem absent_basis_products_independent : finite_independent absent_basis_product.
Proof.
apply: (@finite_independent_separating K I E absent_basis_product
  (fun lambda => hom_as_linear (absent_basis_dual lambda))).
exact: absent_basis_biorthogonal.
Qed.
End Coordinates.
