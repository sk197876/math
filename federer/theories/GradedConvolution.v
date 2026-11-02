(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import Alternating.
From Federer Require Import Convolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the displayed composite is supported in degree p+q.
    Its extension to finite sums gives the actual graded algebra. *)
Section HomogeneousConvolution.
Variable K : fieldType.
Variables X W : lmodType K.
Variable G : grading X.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable D : {linear X -> tensor_space X X}.
Hypothesis hD : preserves_grading G (tensor_grading_product G G) D.

(** Source for [paired_tensor_degree]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma paired_tensor_degree p q (a : Hom_m W G p) (b : Hom_m W G q) n x :
  n != (p+q)%N -> homogeneous (tensor_grading_product G G) n x ->
  paired_tensor hmu a b x = 0.
Proof.
move=> hn; move: x; apply: tensor_component_induction => [|x y hx hy|c x hx|r s x y hrs hx hy].
- exact: linear0.
- by rewrite linearD hx hy add0r.
- rewrite linearZ; change (c *: paired_tensor hmu a b x = 0); by rewrite hx scaler0.
- rewrite paired_tensorE; case hr: (r == p).
  + have hs : s != q.
      apply/eqP=> hs; move/eqP: hr => hr.
      by move: hn; rewrite -hrs hr hs eqxx.
    rewrite (hom_m_degree b hs hy); exact: bil0r.
  + rewrite (hom_m_degree a (negbT hr) hx); exact: bil0l.
Qed.
(** Source for [convolution_degree]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma convolution_degree p q (a : Hom_m W G p) (b : Hom_m W G q) :
  hom_degree G (p+q) (convolution hmu D a b).
Proof. move=> n x hn hx; apply: paired_tensor_degree hn (hD hx). Qed.
(** Source for [homogeneous_convolution]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Definition or construction used to formalise this passage. *)
Definition homogeneous_convolution p q (a : Hom_m W G p) (b : Hom_m W G q) : Hom_m W G (p+q) :=
  @HomogeneousHom K X W G (p+q) (convolution hmu D a b)
    (introT (asboolP _) (convolution_degree a b)).
(** Source for [homogeneous_convolutionE]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma homogeneous_convolutionE p q (a : Hom_m W G p) (b : Hom_m W G q) x :
  homogeneous_convolution a b x = paired_tensor hmu a b (D x).
Proof. by []. Qed.

(** Source for [paired_tensor_bound]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma paired_tensor_bound (a b : Hom X W) N M :
  hom_bounded G a N -> hom_bounded G b M ->
  forall n x, (N+M <= n)%N -> homogeneous (tensor_grading_product G G) n x ->
    paired_tensor hmu a b x = 0.
Proof.
move=> hN hM n x hn; move: x; apply: tensor_component_induction => [|x y hx hy|c x hx|r s x y hrs hx hy].
- exact: linear0.
- by rewrite linearD hx hy add0r.
- rewrite linearZ; change (c *: paired_tensor hmu a b x = 0); by rewrite hx scaler0.
- rewrite paired_tensorE; case: (leqP N r) => hr.
  + rewrite (hN r x hr hx); exact: bil0l.
  + have hs : (M <= s)%N.
      have hsum : (N+M <= r+s)%N by rewrite hrs.
      have h' := leq_trans hsum (leq_add (ltnW hr) (leqnn s)).
      by rewrite leq_add2l in h'.
    rewrite (hM s y hs hy); exact: bil0r.
Qed.
(** Source for [convolution_finite]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma convolution_finite (a b : Hom_finite W G) : hom_finite_pred G (convolution hmu D a b).
Proof.
apply/asboolP; have [N hN] := hom_finite_bound a; have [M hM] := hom_finite_bound b.
exists (N+M)%N; move=> n x hn hx.
exact (@paired_tensor_bound a b N M hN hM n (D x) hn (hD hx)).
Qed.
(** Source for [finite_convolution]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Definition or construction used to formalise this passage. *)
Definition finite_convolution (a b : Hom_finite W G) : Hom_finite W G :=
  @FiniteHom K X W G (convolution hmu D a b) (convolution_finite a b).
(** Source for [finite_convolutionE]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma finite_convolutionE a b x : finite_convolution a b x = paired_tensor hmu a b (D x).
Proof. by []. Qed.
(** Source for [finite_convolution_bilinear]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma finite_convolution_bilinear : bilinear finite_convolution.
Proof.
split.
- move=> b c a a'; apply: hom_finite_ext => x.
  rewrite hom_finite_addE hom_finite_scaleE !finite_convolutionE.
  exact (proj1 (paired_tensor_parameter_bilinear hmu (D x)) b c a a').
- move=> a c b b'; apply: hom_finite_ext => x.
  rewrite hom_finite_addE hom_finite_scaleE !finite_convolutionE.
  exact (proj2 (paired_tensor_parameter_bilinear hmu (D x)) a c b b').
Qed.
(** Source for [finite_convolution_include]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma finite_convolution_include p q (a : Hom_m W G p) (b : Hom_m W G q) :
  finite_convolution (homogeneous_include a) (homogeneous_include b) =
    homogeneous_include (homogeneous_convolution a b).
Proof. apply: hom_finite_ext => x; by []. Qed.
(** Source for [finite_convolution_graded]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma finite_convolution_graded : graded_product (hom_finite_grading W G) finite_convolution.
Proof.
move=> p q a b ha hb.
have hea : a = homogeneous_include (homogeneous_piece p a).
  rewrite homogeneous_pieceK; exact (esym ha).
have heb : b = homogeneous_include (homogeneous_piece q b).
  rewrite homogeneous_pieceK; exact (esym hb).
rewrite {1}hea {1}heb finite_convolution_include.
exact: homogeneous_include_homogeneous.
Qed.
End HomogeneousConvolution.
