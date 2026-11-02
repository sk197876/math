(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import PairingSeparation ScalarTensorContraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: the second construction is the composition of Psi,
    h tensor identity and scalar multiplication. We first construct it
    on the exterior algebra and then prove the required degree bound. *)
Section LeftInteriorHom.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation D := (Psi h2 V).
(** Source for [left_interior_hom]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Definition or construction
    used to formalise this passage. *)
Definition left_interior_hom (zeta : E) (h : Hom E K^o) : E := @contract_tensor K E E h (D zeta).
(** Source for [left_interior_composite]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma left_interior_composite zeta h : left_interior_hom zeta h =
  scalar_tensor E (tensor_map (hom_as_linear h) (linear_id E) (D zeta)).
Proof. by []. Qed.
(** Source for [left_interior_hom_bilinear]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma left_interior_hom_bilinear : bilinear left_interior_hom.
Proof.
split.
- move=> h a x y; by rewrite /left_interior_hom !linearP.
- move=> zeta; exact: (@contract_tensor_parameter_linear K E E).
Qed.
(** Federer 1.5.1: commutativity of the whole displayed diagram. *)
(** Source for [left_interior_diagram]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_diagram zeta h (k : Hom E K^o) :
  k (left_interior_hom zeta h) = convolution (scalar_bilinear K) D h k zeta.
Proof. exact: contract_tensor_pairing. Qed.
(** Source for [left_interior_hom_unique]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem left_interior_hom_unique zeta h y :
  (forall k : Hom E K^o, k y = convolution (scalar_bilinear K) D h k zeta) ->
  y = left_interior_hom zeta h.
Proof. move=> hy; apply: linear_functionals_separate => k; by rewrite hy left_interior_diagram. Qed.
(** Federer 1.5.1, the second final identity. Coassociativity of Psi
    gives associativity of the form product, and the pairing separates. *)
(** Source for [left_interior_hom_associative]: Federer (1969), 1.5.1, p.
    22, last paragraph, the two successive-interior-product identities. In
    words: Right interior multiplication reverses the order of successive
    right factors as displayed; left contraction by an alternating product
    is successive left contraction in the displayed order. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The local LaTeX erratum, p. 1, entry for book p. 22 line 9,
    corrects the multivector degree in the second identity to t. *)
Theorem left_interior_hom_associative zeta a b :
  left_interior_hom zeta (convolution (scalar_bilinear K) D a b) =
    left_interior_hom (left_interior_hom zeta a) b.
Proof.
apply: linear_functionals_separate => k.
have hass := @convolution_associative K E K^o (fun x y : K^o => x*y)
  (scalar_bilinear K) (@mulrA K) D (@Psi_coassociative K h2 V) a b k.
apply: eq_trans (@left_interior_diagram zeta (convolution (scalar_bilinear K) D a b) k) _.
apply: eq_trans (congr1 (fun f : Hom E K^o => f zeta) (esym hass)) _.
apply: eq_trans (esym (@left_interior_diagram zeta a (convolution (scalar_bilinear K) D b k))) _.
exact: esym (@left_interior_diagram (left_interior_hom zeta a) b k).
Qed.
End LeftInteriorHom.
