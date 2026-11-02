(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import ExteriorCore.
From Federer Require Import LinearBasis TensorBasis GradedBasis
  UnitalGradedTensor ExteriorDirectSum ExteriorSmall FiniteCoordinates ExteriorIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.2: e_lambda is a product in increasing order. The recursive
    index below is converted to Federer's Lambda(n,m) after selecting degree m. *)
(** Source for [finite_exterior_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition finite_exterior_basis (K : fieldType) n (b : selection_index n) :=
  @exterior_word K (coordinate_space K n)
    [seq @coordinate_basis K n i | i <- selected_indices n b].
Arguments finite_exterior_basis K n b : clear implicits.

Section CoordinateDirectSum.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n : nat.
Local Notation L := (GRing.Lmodule.clone K K^o _).
Local Notation V := (coordinate_space K n.+1).
Local Notation Q := (coordinate_space K n).
Local Notation f := (GRing.Linear.clone _ _ _ _ (@coordinate_head K n) _).
Local Notation phi := (GRing.Linear.clone _ _ _ _ (@coordinate_head_inclusion K n) _).
Local Notation g := (GRing.Linear.clone _ _ _ _ (@coordinate_tail K n) _).
Local Notation psi := (GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion K n) _).

(** Source for [coordinate_alpha]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_alpha := alpha h2 f g.
(** Source for [coordinate_beta]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_beta := beta phi psi.
(** Source for [coordinate_alphaK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma coordinate_alphaK : cancel coordinate_alpha coordinate_beta.
Proof. exact: (@beta_alpha K h2 V L Q f phi g psi (@coordinate_decomposition K n)). Qed.
(** Source for [coordinate_betaK]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma coordinate_betaK : cancel coordinate_beta coordinate_alpha.
Proof.
exact: (@alpha_beta K h2 V L Q f phi g psi (@coordinate_headK K n)
  (@coordinate_tailK K n) (@coordinate_decomposition K n)).
Qed.

(** Source for [coordinate_beta_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma coordinate_beta_basis (b : bool) (s : selection_index n) :
  coordinate_beta (tensor_inj (exterior_line_basis K b) (finite_exterior_basis K n s)) =
  finite_exterior_basis K n.+1 (b,s).
Proof.
have ht : exterior_algebra_map psi (finite_exterior_basis K n s) =
    exterior_word [seq @coordinate_basis K n.+1 (lift ord0 i) | i <- selected_indices n s].
  rewrite /finite_exterior_basis exterior_algebra_map_word.
  congr 1 (exterior_word _); rewrite -map_comp.
  apply: eq_map => i; exact: (@coordinate_tail_basis K n i).
have hp : exterior_algebra_map phi (exterior_line_basis K b) =
    if b then exterior_generator (@coordinate_basis K n.+1 ord0) else exterior_unit V.
  rewrite /exterior_line_basis; case: b.
  - exact: eq_trans (@exterior_algebra_mapE K L V phi (1 : K^o))
      (congr1 (@exterior_generator K V) (@coordinate_head_basis K n)).
  - exact: (algebra_map_one (exterior_algebra_map phi)).
apply: eq_trans (@betaE K V L Q phi psi (exterior_line_basis K b) (finite_exterior_basis K n s)) _.
apply: eq_trans (congr2 (@wedge K V) hp ht) _.
clear hp ht; by case: b; rewrite /finite_exterior_basis /= -map_comp ?exterior_word_cons ?wedge_unitl.
Qed.
End CoordinateDirectSum.

(** Federer 1.3.2, basis argument: induction splits off a line, uses
    wedge* R = R direct-sum R, and applies the signed tensor-product
    isomorphism. No basis theorem for exterior powers is assumed. *)
Section FiniteBasis.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Local Notation L := (GRing.Lmodule.clone K K^o _).

(** Source for [finite_exterior_basisP]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem finite_exterior_basisP n : is_basis (finite_exterior_basis K n).
Proof.
elim: n => [|n ih].
- exact: (@exterior_zero_basisP K (coordinate_space K 0) (@coordinate_zero K)).
have ht := @tensor_basisP K (Choice.clone bool _) (Choice.clone (selection_index n) _)
  (exterior_space L) (exterior_space (coordinate_space K n))
  (exterior_line_basis K) (finite_exterior_basis K n) (exterior_line_basisP K) ih.
have hb := @basis_transport K (Choice.clone (selection_index n.+1) _)
  (unital_tensor_algebra (exterior_unital L) (exterior_unital (coordinate_space K n)) true)
  (exterior_space (coordinate_space K n.+1))
  (tensor_basis (exterior_line_basis K) (finite_exterior_basis K n))
  (coordinate_beta K n) (coordinate_alpha h2 n)
  (@coordinate_betaK K h2 n) (@coordinate_alphaK K h2 n) ht.
apply: basis_congr _ hb => [[b s]].
exact: (@coordinate_beta_basis K n b s).
Qed.

(** Source for [finite_exterior_basis_homogeneous]: Federer (1969), 1.3.2,
    pp. 14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_exterior_basis_homogeneous n (b : selection_index n) :
  homogeneous (exterior_grading (coordinate_space K n))
    (size (selected_indices n b)) (finite_exterior_basis K n b).
Proof.
have h := exterior_word_homogeneous [seq @coordinate_basis K n i | i <- selected_indices n b].
by rewrite size_map in h.
Qed.
(** Source for [finite_exterior_graded_basis]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Theorem finite_exterior_graded_basis n :
  is_graded_basis (exterior_grading (coordinate_space K n))
    (finite_exterior_basis K n) (fun b => size (selected_indices n b)).
Proof. split; [exact: finite_exterior_basisP | exact: finite_exterior_basis_homogeneous]. Qed.
End FiniteBasis.
