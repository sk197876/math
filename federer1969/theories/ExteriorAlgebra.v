(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  TensorAlgebra SquareZeroWords ModuleQuotient AlgebraQuotient ExteriorUP ExteriorIdeal ExteriorAlgebraUP.
From Federer Require Export WordEvaluation ExteriorSealed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1: the exterior algebra of V, its products and the
    extension of square-zero linear maps. Everything follows from the
    property [is_exterior_power_algebra] of the sealed exterior algebra. *)
Section ExteriorAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation iota := (exterior_generator_map V).
Local Notation H := (exterior_algebraP V).

(** Source for [exterior_space]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_space : lmodType K := exterior_algebra V.

(** Source for [wedge]: Federer (1969), 1.3.1, p. 13, quotient definition
    and exterior-multiplication paragraph. In words: The quotient by the
    square-generated ideal is the exterior algebra; products descend to
    wedge products, and the zeroth and first powers identify with R and V.
    Definition or construction used to formalise this passage. *)
Definition wedge (x y : exterior_space) : exterior_space :=
  alg_mul (exterior_algebra V) x y.
(** Source for [exterior_unit]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_unit : exterior_space := alg_one (exterior_algebra V).
(** Source for [exterior_word]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_word (s : seq V) : exterior_space := word_eval iota s.
(** Source for [exterior_generator]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_generator (v : V) := exterior_word [:: v].

(** Source for [exterior_generator_mapE]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_generator_mapE v : iota v = exterior_generator v.
Proof. by rewrite /exterior_generator /exterior_word /= alg_unitr. Qed.

(** Source for [exterior_generator_linear]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_generator_linear : linear exterior_generator.
Proof. by move=> a v w; rewrite -!exterior_generator_mapE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V exterior_space
  *:%R exterior_generator exterior_generator_linear.

(** Source for [wedge_bilinear]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma wedge_bilinear : bilinear wedge.
Proof. exact: alg_bilinear. Qed.
(** Source for [wedge_assoc]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma wedge_assoc : associative wedge.
Proof. exact: alg_assoc. Qed.
(** Source for [wedge_unitl]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma wedge_unitl : left_id exterior_unit wedge.
Proof. exact: alg_unitl. Qed.
(** Source for [wedge_unitr]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma wedge_unitr : right_id exterior_unit wedge.
Proof. exact: alg_unitr. Qed.

(** Source for [exterior_word_cat]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma exterior_word_cat s t :
  wedge (exterior_word s) (exterior_word t) = exterior_word (s ++ t).
Proof. by rewrite /wedge /exterior_word word_eval_cat. Qed.
(** Source for [exterior_word_nil]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma exterior_word_nil : exterior_word [::] = exterior_unit.
Proof. by []. Qed.
(** Source for [exterior_word_cons]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma exterior_word_cons v s :
  exterior_word (v :: s) = wedge (exterior_generator v) (exterior_word s).
Proof. exact: esym (exterior_word_cat [:: v] s). Qed.

(** Federer 1.3.1, second paragraph: products span. *)
(** Source for [exterior_word_induction]: Federer (1969), 1.3.1, p. 13,
    paragraph on products of m vectors. In words: Products of m vectors span
    the m-th exterior power; the canonical tensor-to-exterior map takes a
    tensor word to the corresponding exterior product. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma exterior_word_induction (P : exterior_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, P (exterior_word s)) : forall x, P x.
Proof. exact: (alt_word_induction H h0 hD hZ hw). Qed.

(** Source for [exterior_algebra_induction]: Federer (1969), 1.3.1, p. 13,
    paragraph on products of m vectors. In words: Products of m vectors span
    the m-th exterior power; the canonical tensor-to-exterior map takes a
    tensor word to the corresponding exterior product. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma exterior_algebra_induction (P : exterior_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (h1 : P exterior_unit) (hV : forall v, P (exterior_generator v))
    (hm : forall x y, P x -> P y -> P (wedge x y)) : forall x, P x.
Proof.
apply: exterior_word_induction => // s.
elim: s => [|v s ih]; first exact: h1.
rewrite exterior_word_cons; exact: hm (hV v) ih.
Qed.

(** Federer 1.3.1, first and third paragraphs: the generating squares vanish. *)
(** Source for [exterior_generator_square]: Federer (1969), 1.3.1, p. 13,
    opening paragraph defining the ideal mV. In words: The two-sided ideal
    generated by all x tensor x is homogeneous, with no degree-zero or
    degree-one component. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_generator_square v : wedge (exterior_generator v) (exterior_generator v) = 0.
Proof. by rewrite -exterior_generator_mapE; exact: (exterior_square H v). Qed.

(** Source for [exterior_generator_skew]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma exterior_generator_skew v w :
  wedge (exterior_generator v) (exterior_generator w) =
    - wedge (exterior_generator w) (exterior_generator v).
Proof. by rewrite -!exterior_generator_mapE; exact: (square_zero_skew (exterior_square H) v w). Qed.

(** Federer 1.3.1, second paragraph: the canonical homomorphism of the
    tensor algebra onto the exterior algebra. *)
(** Source for [exterior_projection]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_projection : algebra_map (tensor_algebra V) (exterior_algebra V) :=
  tensor_algebra_extension iota.

(** Source for [exterior_projection_word]: Federer (1969), 1.3.1, p. 13,
    paragraph on products of m vectors. In words: Products of m vectors span
    the m-th exterior power; the canonical tensor-to-exterior map takes a
    tensor word to the corresponding exterior product. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma exterior_projection_word s : exterior_projection (tensor_word s) = exterior_word s.
Proof. exact: tensor_algebra_extension_word. Qed.

(** Source for [wedge_projection]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma wedge_projection x y :
  wedge (exterior_projection x) (exterior_projection y) =
  exterior_projection (tensor_product x y).
Proof. by rewrite /wedge -algebra_map_mul. Qed.

(** Federer 1.3.1, universal mapping property. *)
Section Extension.
Variable A : algebra K.
Variable f : {linear V -> A}.
Hypothesis square_zero : forall v, alg_mul A (f v) (f v) = 0.

(** Source for [exterior_relation_killed]: Federer (1969), 1.3.1, p. 13,
    opening paragraph defining the ideal mV. In words: The two-sided ideal
    generated by all x tensor x is homogeneous, with no degree-zero or
    degree-one component. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_relation_killed x : mV V x -> tensor_algebra_extension f x = 0.
Proof.
elim=> [|u v hu ihu hv ihv|a u hu ihu|s t v].
- exact: linear0.
- by rewrite linearD ihu ihv add0r.
- by rewrite linearZ_LR ihu scaler0.
rewrite tensor_algebra_extension_word word_eval_cat /=.
rewrite (@alg_assoc K A (f v) (f v) (word_eval f t)) square_zero.
by rewrite (bil0l (alg_bilinear A)) (bil0r (alg_bilinear A)).
Qed.

(** Source for [exterior_algebra_extension]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Definition or construction
    used to formalise this passage. The square-zero target condition is used
    in the proof on p. 14. The abstract ungraded square-zero property
    formalised here is stronger than the printed graded anticommutative
    formulation and also works in characteristic two. *)
Definition exterior_algebra_extension : algebra_map (exterior_algebra V) A :=
  alt_extension H square_zero.

(** Source for [exterior_algebra_extension_word]: Federer (1969), 1.3.1, p.
    14, universal mapping property and its proof. In words: The
    tensor-algebra extension factors through the exterior quotient precisely
    when the images of the generators have square zero. Supporting lemma for
    this passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Lemma exterior_algebra_extension_word s :
  exterior_algebra_extension (exterior_word s) = word_eval f s.
Proof. exact: alt_extension_word. Qed.

(** Source for [exterior_algebra_extension_generator]: Federer (1969),
    1.3.1, p. 14, universal mapping property and its proof. In words: The
    tensor-algebra extension factors through the exterior quotient precisely
    when the images of the generators have square zero. Supporting lemma for
    this passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Lemma exterior_algebra_extension_generator v :
  exterior_algebra_extension (exterior_generator v) = f v.
Proof. by rewrite exterior_algebra_extension_word /= alg_unitr. Qed.

(** Source for [exterior_algebra_extension_projection]: Federer (1969),
    1.3.1, p. 14, universal mapping property and its proof. In words: The
    tensor-algebra extension factors through the exterior quotient precisely
    when the images of the generators have square zero. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The square-zero target condition is used in the proof on p. 14.
    The abstract ungraded square-zero property formalised here is stronger
    than the printed graded anticommutative formulation and also works in
    characteristic two. *)
Lemma exterior_algebra_extension_projection x :
  exterior_algebra_extension (exterior_projection x) = tensor_algebra_extension f x.
Proof.
have e : forall v, algebra_comp exterior_algebra_extension exterior_projection
    (tensor_generator v) = f v.
  move=> v; change (exterior_algebra_extension (exterior_projection (tensor_word [:: v]))
    = f v).
  by rewrite exterior_projection_word exterior_algebra_extension_word /= alg_unitr.
exact: (tensor_algebra_extension_unique e x).
Qed.

(** Source for [exterior_algebra_extension_unique]: Federer (1969), 1.3.1,
    p. 14, universal mapping property and its proof. In words: The
    tensor-algebra extension factors through the exterior quotient precisely
    when the images of the generators have square zero. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The square-zero target condition is used in the proof on p. 14.
    The abstract ungraded square-zero property formalised here is stronger
    than the printed graded anticommutative formulation and also works in
    characteristic two. *)
Lemma exterior_algebra_extension_unique (g : algebra_map (exterior_algebra V) A) :
  (forall v, g (exterior_generator v) = f v) ->
  forall x, g x = exterior_algebra_extension x.
Proof.
move=> e; apply: alt_extension_unique => v.
by rewrite exterior_generator_mapE e.
Qed.
End Extension.

(** Source for [exterior_algebra_exists]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Supporting lemma for this
    passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Theorem exterior_algebra_exists :
  @is_exterior_algebra K V (exterior_algebra V)
    (GRing.Linear.clone _ _ _ _ exterior_generator _).
Proof.
split; first exact: exterior_generator_square.
move=> A f hf; exists (exterior_algebra_extension hf); split.
  exact: exterior_algebra_extension_generator.
exact: exterior_algebra_extension_unique.
Qed.
End ExteriorAlgebra.
Arguments exterior_word {K V} s : simpl never.
