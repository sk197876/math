(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.
From Federer Require Import Convolution GradedConvolution
  ConvolutionAssociativity ConvolutionCommutativity ConvolutionNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the alternating algebra with coefficients in W,
    and the corresponding product of homogeneous alternating forms. *)
Section AlternatingProduct.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Local Notation E := (exterior_unital V).
Local Notation G := (exterior_grading V).
Local Notation D := (Psi h2 V).
Local Notation hD := (@Psi_graded K h2 V).
(** Source for [alternating_wedge]: Federer (1969), 1.4.2, p. 18, definition
    by the displayed composite through the diagonal. In words: The
    alternating product is the diagonal followed by the tensor of the two
    forms and coefficient multiplication; degrees p and q give degree p+q.
    Definition or construction used to formalise this passage. *)
Definition alternating_wedge (a b : A_star V W) : A_star V W := finite_convolution hmu hD a b.
(** Source for [alternating_wedgeE]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma alternating_wedgeE a b x : alternating_wedge a b x = paired_tensor hmu a b (D x).
Proof. by []. Qed.
(** Source for [alternating_wedge_composite]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma alternating_wedge_composite a b x :
  alternating_wedge a b x = nu hmu (tensor_map (hom_as_linear a) (hom_as_linear b) (D x)).
Proof. exact: paired_tensor_factorisation. Qed.
(** Source for [alternating_wedge_bilinear]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma alternating_wedge_bilinear : bilinear alternating_wedge.
Proof. exact: finite_convolution_bilinear. Qed.
(** Source for [alternating_wedge_graded]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma alternating_wedge_graded : graded_product (A_star_grading V W) alternating_wedge.
Proof. exact: finite_convolution_graded. Qed.
(** Source for [alternating_algebra]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Definition or construction used to formalise this passage. *)
Definition alternating_algebra : graded_algebra K :=
  @GradedAlgebra K (A_star V W) (A_star_grading V W) alternating_wedge
    alternating_wedge_bilinear alternating_wedge_graded.

(** Source for [form_wedge]: Federer (1969), 1.4.2, p. 18, definition by the
    displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Definition
    or construction used to formalise this passage. *)
Definition form_wedge p q (a : A_m V W p) (b : A_m V W q) : A_m V W (p+q) :=
  homogeneous_form (homogeneous_convolution hmu hD (form_homogeneous a) (form_homogeneous b)).
(** Source for [form_wedge_include]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_wedge_include p q (a : A_m V W p) (b : A_m V W q) :
  form_include (form_wedge a b) = alternating_wedge (form_include a) (form_include b).
Proof.
rewrite /form_wedge /form_include homogeneous_formK /alternating_wedge.
exact (esym (@finite_convolution_include K E W G mu hmu D hD p q
  (form_homogeneous a) (form_homogeneous b))).
Qed.
(** Source for [form_wedgeE]: Federer (1969), 1.4.2, p. 18, definition by
    the displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_wedgeE p q (a : A_m V W p) (b : A_m V W q) (t : (p+q).-tuple V) :
  form_wedge a b t = paired_tensor hmu (form_homogeneous a) (form_homogeneous b) (D (exterior_word t)).
Proof. by []. Qed.
(** Source for [form_wedge_bilinear]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_wedge_bilinear p q : bilinear (@form_wedge p q).
Proof.
split.
- move=> b c a a'; apply: (can_inj (@form_includeK K V W (p+q))).
  rewrite linearP !form_wedge_include !linearP.
  change (alternating_wedge (c *: form_include a + form_include a') (form_include b) =
    c *: form_include (form_wedge a b) + form_include (form_wedge a' b)).
  rewrite !form_wedge_include; exact: (proj1 alternating_wedge_bilinear).
- move=> a c b b'; apply: (can_inj (@form_includeK K V W (p+q))).
  rewrite linearP !form_wedge_include !linearP.
  change (alternating_wedge (form_include a) (c *: form_include b + form_include b') =
    c *: form_include (form_wedge a b) + form_include (form_wedge a b')).
  rewrite !form_wedge_include; exact: (proj2 alternating_wedge_bilinear).
Qed.

(** Source for [alternating_Psi_coassociative]: Federer (1969), 1.4.2, p.
    18, first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma alternating_Psi_coassociative x :
  tensor_associator E E E (tensor_map D (linear_id E) (D x)) =
    tensor_map (linear_id E) D (D x).
Proof. exact: Psi_coassociative. Qed.
(** Source for [alternating_wedge_associative]: Federer (1969), 1.4.2, p.
    18, first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem alternating_wedge_associative : associative mu -> associative alternating_wedge.
Proof.
move=> hA a b c; apply: val_inj.
exact (@convolution_associative K E W mu hmu hA D alternating_Psi_coassociative a b c).
Qed.
(** Source for [alternating_wedge_anticommutative]: Federer (1969), 1.4.2,
    p. 18, second consequence of the diagonal properties. In words:
    Commutative coefficient multiplication gives graded anticommutative
    alternating multiplication. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem alternating_wedge_anticommutative : commutative mu ->
  graded_anticommutative (A_star_grading V W) alternating_wedge.
Proof.
move=> hC p q a b ha hb.
have hea : a = homogeneous_include (homogeneous_piece p a).
  rewrite homogeneous_pieceK; exact (esym ha).
have heb : b = homogeneous_include (homogeneous_piece q b).
  rewrite homogeneous_pieceK; exact (esym hb).
move: hea heb => -> ->; apply: hom_finite_ext => x.
rewrite hom_finite_scaleE.
exact (@convolution_anticommutative K E W G mu hmu hC p q
  (homogeneous_piece p a) (homogeneous_piece q b) D
  (@Psi_anticommutative K h2 V) x).
Qed.
End AlternatingProduct.

(** Federer 1.4.2, multiplicativity of A^*(f,W). *)
Section Naturality.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V V' W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable f : {linear V -> V'}.
(** Source for [A_star_dual_multiplicative]: Federer (1969), 1.4.2, p. 18,
    fourth consequence of the diagonal properties. In words: Pullback along
    a linear map is multiplicative for the alternating product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem A_star_dual_multiplicative (a b : A_star V' W) :
  A_star_dual f (alternating_wedge h2 hmu a b) =
    alternating_wedge h2 hmu (A_star_dual f a) (A_star_dual f b).
Proof.
apply: val_inj.
exact (@convolution_natural K (exterior_space V) (exterior_space V') W mu hmu
  (exterior_algebra_map f) (Psi h2 V) (Psi h2 V') (@Psi_natural K h2 V V' f) a b).
Qed.
End Naturality.
