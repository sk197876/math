(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, first displayed composite: nu(s tensor t)=s*t.
    No associativity, commutativity or unit is built into this definition;
    each additional law will be used under its stated hypothesis. *)
Section CoefficientProduct.
Variable K : fieldType.
Variables X Y W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
(** Source for [nu]: Federer (1969), 1.4.2, p. 18, definition by the
    displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Definition
    or construction used to formalise this passage. *)
Definition nu : {linear tensor_space W W -> W} := tensor_lift hmu.
(** Source for [nuE]: Federer (1969), 1.4.2, p. 18, definition by the
    displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma nuE s t : nu (tensor_inj s t) = mu s t.
Proof. exact: tensor_liftE. Qed.

(** Source for [paired_tensor_bilinear]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma paired_tensor_bilinear (a : Hom X W) (b : Hom Y W) :
  bilinear (fun x y => mu (a x) (b y)).
Proof.
split.
- by move=> y c x x'; rewrite (hom_linear a) (proj1 hmu).
- by move=> x c y y'; rewrite (hom_linear b) (proj2 hmu).
Qed.
(** Source for [paired_tensor]: Federer (1969), 1.4.2, p. 18, definition by
    the displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Definition
    or construction used to formalise this passage. *)
Definition paired_tensor (a : Hom X W) (b : Hom Y W) : {linear tensor_space X Y -> W} :=
  tensor_lift (paired_tensor_bilinear a b).
(** Source for [paired_tensorE]: Federer (1969), 1.4.2, p. 18, definition by
    the displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma paired_tensorE a b x y : paired_tensor a b (tensor_inj x y) = mu (a x) (b y).
Proof. exact: tensor_liftE. Qed.
(** Source for [paired_tensor_factorisation]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma paired_tensor_factorisation a b x :
  paired_tensor a b x = nu (tensor_map (hom_as_linear a) (hom_as_linear b) x).
Proof.
apply: (tensor_ext (tensor_exists X Y) (paired_tensor a b)
  (linear_comp nu (tensor_map (hom_as_linear a) (hom_as_linear b)))) x => u v.
by rewrite paired_tensorE /linear_comp /= tensor_mapE nuE.
Qed.
(** Source for [paired_tensor_parameter_bilinear]: Federer (1969), 1.4.2, p.
    18, definition by the displayed composite through the diagonal. In
    words: The alternating product is the diagonal followed by the tensor of
    the two forms and coefficient multiplication; degrees p and q give
    degree p+q. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma paired_tensor_parameter_bilinear x :
  bilinear (fun (a : Hom X W) (b : Hom Y W) => paired_tensor a b x).
Proof.
elim/tensor_induction: x => [|x y [hxl hxr] [hyl hyr]|c x [hxl hxr]|u v]; split.
- by move=> b c a a'; rewrite !linear0 add0r.
- by move=> a c b b'; rewrite !linear0 add0r.
- move=> b c a a'.
  rewrite (linD (linearP (paired_tensor (c *: a + a') b)) x y)
    (linD (linearP (paired_tensor a b)) x y)
    (linD (linearP (paired_tensor a' b)) x y).
  change (paired_tensor (c *: a + a') b x + paired_tensor (c *: a + a') b y =
    c *: (paired_tensor a b x + paired_tensor a b y) +
    (paired_tensor a' b x + paired_tensor a' b y)).
  by rewrite hxl hyl scalerDr addrACA.
- move=> a c b b'.
  rewrite (linD (linearP (paired_tensor a (c *: b + b'))) x y)
    (linD (linearP (paired_tensor a b)) x y)
    (linD (linearP (paired_tensor a b')) x y).
  change (paired_tensor a (c *: b + b') x + paired_tensor a (c *: b + b') y =
    c *: (paired_tensor a b x + paired_tensor a b y) +
    (paired_tensor a b' x + paired_tensor a b' y)).
  by rewrite hxr hyr scalerDr addrACA.
- move=> b d a a'.
  rewrite (linZ (linearP (paired_tensor (d *: a + a') b)) c x)
    (linZ (linearP (paired_tensor a b)) c x)
    (linZ (linearP (paired_tensor a' b)) c x).
  by rewrite hxl scalerDr !scalerA [c * d]mulrC.
- move=> a d b b'.
  rewrite (linZ (linearP (paired_tensor a (d *: b + b'))) c x)
    (linZ (linearP (paired_tensor a b)) c x)
    (linZ (linearP (paired_tensor a b')) c x).
  by rewrite hxr scalerDr !scalerA [c * d]mulrC.
- by move=> b c a a'; rewrite !paired_tensorE hom_addE hom_scaleE (proj1 hmu).
- by move=> a c b b'; rewrite !paired_tensorE hom_addE hom_scaleE (proj2 hmu).
Qed.
End CoefficientProduct.

Section Convolution.
Variable K : fieldType.
Variables X W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable D : {linear X -> tensor_space X X}.
(** Source for [convolution]: Federer (1969), 1.4.2, p. 18, definition by
    the displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Definition
    or construction used to formalise this passage. *)
Definition convolution (a b : Hom X W) : Hom X W :=
  hom_of_linear (linear_comp (paired_tensor hmu a b) D).
(** Source for [convolutionE]: Federer (1969), 1.4.2, p. 18, definition by
    the displayed composite through the diagonal. In words: The alternating
    product is the diagonal followed by the tensor of the two forms and
    coefficient multiplication; degrees p and q give degree p+q. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma convolutionE a b x : convolution a b x = paired_tensor hmu a b (D x).
Proof. by []. Qed.
(** Source for [convolution_factorisation]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma convolution_factorisation a b x :
  convolution a b x = nu hmu (tensor_map (hom_as_linear a) (hom_as_linear b) (D x)).
Proof. exact: paired_tensor_factorisation. Qed.
(** Source for [convolution_bilinear]: Federer (1969), 1.4.2, p. 18,
    definition by the displayed composite through the diagonal. In words:
    The alternating product is the diagonal followed by the tensor of the
    two forms and coefficient multiplication; degrees p and q give degree
    p+q. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma convolution_bilinear : bilinear convolution.
Proof.
split.
- move=> b c a a'; apply: hom_ext => x.
  rewrite hom_addE hom_scaleE !convolutionE; exact: (proj1 (paired_tensor_parameter_bilinear hmu (D x))).
- move=> a c b b'; apply: hom_ext => x.
  rewrite hom_addE hom_scaleE !convolutionE; exact: (proj2 (paired_tensor_parameter_bilinear hmu (D x))).
Qed.
End Convolution.
