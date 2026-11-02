(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import ScalarTensorContraction LeftInteriorHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: the composition through the diagonal map sends a q-vector
    and a p-covector to a (q-p)-vector. *)
Section Degree.
Variable K : fieldType.
Variable X : lmodType K.
Variable G : grading X.
Variables p q : nat.
(** Source for [contract_tensor_degree]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma contract_tensor_degree (h : Hom_m K^o G p) t :
  homogeneous (tensor_grading_product G G) q t ->
    homogeneous G (q-p) (@contract_tensor K X X h t).
Proof.
move: t; apply: tensor_component_induction => [|s t hs ht|a t ht|r s x y hrs hx hy].
- rewrite linear0; exact: homogeneous0.
- rewrite linearD; exact: homogeneousD hs ht.
- rewrite linearZ; exact: homogeneousZ ht.
- rewrite contract_tensorE; case hr: (r == p).
  + move/eqP: hr => hr.
    have hdeg : (q-p=s)%N by rewrite -hrs -hr addKn.
    rewrite hdeg; exact: homogeneousZ hy.
  + rewrite (hom_m_degree h (negbT hr) hx) scale0r; exact: homogeneous0.
Qed.
End Degree.
Section ExteriorDegree.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables p q : nat.
(** Source for [left_interior_degree]: Federer (1969), 1.5.1, p. 22,
    diagonal-map composite and commutative diagram. In words: Apply the
    diagonal, evaluate the first factor against the homogeneous covector,
    then use scalar multiplication on the remaining factor; the diagram
    proves the characteristic pairing identity. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem left_interior_degree (zeta : exterior_power V q) (a : A_m V K^o p) :
  homogeneous (exterior_grading V) (q-p)
    (left_interior_hom h2 (component_val zeta) (form_homogeneous a)).
Proof.
apply: contract_tensor_degree.
exact: Psi_graded (component_homogeneous zeta).
Qed.
End ExteriorDegree.
