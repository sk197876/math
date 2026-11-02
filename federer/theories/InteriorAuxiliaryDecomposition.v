(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.
From Federer Require Import RightCovectorConvolution InteriorOneDegree InteriorNilpotency.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: extensionality through the identification of 1.4.1. *)
(** Source for [form_hom_ext]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_hom_ext (K : fieldType) (V W : lmodType K) m (f g : A_m V W m) :
  (forall x, form_homogeneous f x = form_homogeneous g x) -> f = g.
Proof.
move=> h; apply: (can_inj (@form_homogeneousK K V W m)); exact: hom_m_ext.
Qed.
(** Source for [form_hom_addE]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_hom_addE (K : fieldType) (V W : lmodType K) m (f g : A_m V W m) x :
  form_homogeneous (f+g) x = form_homogeneous f x + form_homogeneous g x.
Proof. by rewrite linearD hom_m_addE. Qed.
(** Source for [form_hom_zeroE]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_hom_zeroE (K : fieldType) (V W : lmodType K) m x :
  form_homogeneous (0 : A_m V W m) x = 0.
Proof. by rewrite linear0 hom_m_zeroE. Qed.

(** Federer 1.5.3, the decomposition used in the proof. The names beta
    and psi retain their roles in phi=beta wedge alpha+psi. The assertion
    about beta uses Hom, also when beta has degree zero (j=1). *)
Module FedererInteriorDecomposition.
Section Decomposition.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Hypothesis hv : one_hom alpha v = 1.
Local Notation E := (exterior_space V).
Local Notation ev := (exterior_generator v).
Local Notation R := (v_interior v).
Local Notation W := (wedge_alpha h2 alpha).
(** Source for [beta]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Definition or construction used to formalise this passage. *)
Definition beta n (phi : A_m V K^o n.+1) : A_m V K^o n := R phi.
(** Source for [psi]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Definition or construction used to formalise this passage. *)
Definition psi n (phi : A_m V K^o n.+1) : A_m V K^o n.+1 := R (W phi).
(** Source for [beta_annihilated]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma beta_annihilated n (phi : A_m V K^o n.+1) :
  right_interior_hom ev (form_homogeneous (beta phi)) = 0.
Proof. rewrite /beta v_interior_hom; exact: right_interior_square. Qed.
(** Source for [psi_annihilated]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma psi_annihilated n (phi : A_m V K^o n.+1) :
  right_interior_hom ev (form_homogeneous (psi phi)) = 0.
Proof. rewrite /psi v_interior_hom; exact: right_interior_square. Qed.
(** Source for [auxiliary_decomposition]: Federer (1969), 1.5.3, p. 23,
    first display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem auxiliary_decomposition n (phi : A_m V K^o n.+1) :
  phi = W (beta phi) + psi phi.
Proof.
apply: form_hom_ext => x; rewrite form_hom_addE /psi /beta
  v_interior_homE !wedge_alpha_homE v_interior_hom.
rewrite right_covector_product hv mul1r addrC subrK; by [].
Qed.
(** Source for [auxiliary_decomposition_exists]: Federer (1969), 1.5.3, p.
    23, first display and auxiliary decomposition in its proof. In words: If
    a one-covector alpha takes value one on v, every positive-degree form is
    v contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem auxiliary_decomposition_exists n (phi : A_m V K^o n.+1) :
  exists (beta : A_m V K^o n) (psi : A_m V K^o n.+1),
    phi = W beta + psi /\
    right_interior_hom ev (form_homogeneous beta) = 0 /\
    right_interior_hom ev (form_homogeneous psi) = 0.
Proof.
exists (beta phi), (psi phi); split; first exact: auxiliary_decomposition.
split; [exact: beta_annihilated | exact: psi_annihilated].
Qed.
(** Federer 1.5.3, first display, with j=n+1. *)
(** Source for [interior_decomposition]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem interior_decomposition n (phi : A_m V K^o n.+1) :
  phi = R (W phi) + W (R phi).
Proof. rewrite addrC; exact: auxiliary_decomposition. Qed.
End Decomposition.
End FedererInteriorDecomposition.
