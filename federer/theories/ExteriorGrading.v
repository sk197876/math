(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require boolp.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedSums
  GradedComponents FamilyUpdate TensorFamilyUP WordEvaluation PowerWords
  TensorAlgebraUP TensorAlgebra TensorGrading TensorPowers ExteriorIdeal
  ExteriorAlgebraUP ExteriorSealed ExteriorAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1, first paragraph: the grading of the exterior algebra.
    Elements of exterior_power are Federer's m-vectors. Everything follows
    from [is_exterior_power_algebra]. *)
Section ExteriorGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation H := (exterior_algebraP V).

(** Source for [exterior_degree]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Definition or construction used to formalise this passage. *)
Definition exterior_degree n : {linear E -> E} := grade (exterior_grading V) n.
(** Source for [exterior_power]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Definition or construction used to formalise this passage. *)
Definition exterior_power n := graded_component (exterior_grading V) n.
HB.instance Definition _ n := GRing.Lmodule.copy (exterior_power n)
  (graded_component (exterior_grading V) n).

(** Source for [exterior_word_homogeneous]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_word_homogeneous s :
  homogeneous (exterior_grading V) (size s) (exterior_word s).
Proof. exact: alt_word_homogeneous H s. Qed.

(** Source for [exterior_degree_word]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_degree_word n s :
  exterior_degree n (exterior_word s) = if size s == n then exterior_word s else 0.
Proof.
rewrite /exterior_degree (grade_homogeneous _ (exterior_word_homogeneous s)).
by rewrite eq_sym.
Qed.

(** Source for [exterior_degree_orthogonal]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_degree_orthogonal m n x :
  exterior_degree m (exterior_degree n x) = if m == n then exterior_degree n x else 0.
Proof. exact: grade_orthogonal. Qed.
(** Source for [exterior_degree_finite]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_degree_finite x : exists N, x = \sum_(i < N) exterior_degree i x.
Proof. exact: grade_finite. Qed.

(** Source for [exterior_unit_homogeneous]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_unit_homogeneous : homogeneous (exterior_grading V) 0 (exterior_unit V).
Proof. exact: (exterior_word_homogeneous [::]). Qed.
(** Source for [exterior_generator_homogeneous]: Federer (1969), 1.3.1, p.
    13, homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_generator_homogeneous v :
  homogeneous (exterior_grading V) 1 (exterior_generator v).
Proof. exact: (exterior_word_homogeneous [:: v]). Qed.

(** Source for [exterior_degree_projection]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_degree_projection n x :
  exterior_degree n (exterior_projection V x) = exterior_projection V (tensor_degree n x).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_degree_word exterior_projection_word exterior_degree_word.
by case: ifP => _; rewrite ?exterior_projection_word ?linear0.
Qed.

(** Source for [exterior_projection_graded]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_projection_graded :
  preserves_grading (tensor_grading V) (exterior_grading V) (exterior_projection V).
Proof.
move=> n x hx; rewrite /homogeneous -/(exterior_degree n _).
by rewrite exterior_degree_projection hx.
Qed.

(** Source for [wedge_components]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma wedge_components m n x y :
  homogeneous (exterior_grading V) (m + n)%N
    (wedge (exterior_degree m x) (exterior_degree n y)).
Proof.
have b := wedge_bilinear V.
elim/exterior_word_induction: x => [|x x' hx hx'|a x hx|s].
- by rewrite linear0 (bil0l b); exact: homogeneous0.
- by rewrite linearD (bilDl b); exact: homogeneousD.
- by rewrite linearZ (bilZl b); exact: homogeneousZ.
elim/exterior_word_induction: y => [|y y' hy hy'|a y hy|t].
- by rewrite linear0 (bil0r b); exact: homogeneous0.
- by rewrite linearD (bilDr b); exact: homogeneousD.
- by rewrite linearZ (bilZr b); exact: homogeneousZ.
rewrite !exterior_degree_word.
case: (eqVneq (size s) m) => [<-|_]; last first.
  by rewrite (bil0l b); exact: homogeneous0.
case: (eqVneq (size t) n) => [<-|_]; last first.
  by rewrite (bil0r b); exact: homogeneous0.
by rewrite exterior_word_cat -size_cat; exact: exterior_word_homogeneous.
Qed.

(** Source for [wedge_graded]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma wedge_graded : graded_product (exterior_grading V) (@wedge K V).
Proof.
move=> m n x y hx hy.
by rewrite -hx -hy; exact: wedge_components.
Qed.

(** Source for [graded_exterior_algebra]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Definition or construction used to formalise this
    passage. *)
Definition graded_exterior_algebra : graded_algebra K :=
  @GradedAlgebra K E (exterior_grading V) (@wedge K V) (wedge_bilinear V) wedge_graded.

(** Federer 1.3.1, second paragraph: products of exactly m vectors span
    the space of m-vectors. *)
(** Source for [exterior_component_induction]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_component_induction n (P : E -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, size s = n -> P (exterior_word s)) :
    forall x, homogeneous (exterior_grading V) n x -> P x.
Proof.
have hp : forall x, P (exterior_degree n x).
  apply: exterior_word_induction => [|x y hx hy|a x hx|s].
  - by rewrite linear0.
  - rewrite linearD; exact: hD hx hy.
  - rewrite linearZ; exact: hZ hx.
  rewrite exterior_degree_word; case: ifP => [/eqP hs|_]; last exact: h0.
  exact: hw hs.
by move=> x hx; rewrite -hx; exact: hp.
Qed.

(** Federer 1.4.1: a multilinear function on words vanishing on words with
    a repeated vector extends uniquely to a linear map on the exterior
    algebra, assembled from the universal properties of the components. *)
Section AlternatingWords.
Variable Z : lmodType K.
Variable beta : seq V -> Z.
Hypothesis hb : multilinear_words beta.
Hypothesis ha : forall s, ~~ uniq s -> beta s = 0.

(** Source for [alternating_word_component]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition alternating_word_component m
    (x : {dffun forall i : 'I_m, power_family V m i}) : Z := beta (power_seq x).

(** Source for [alternating_word_component_multilinear]: Federer (1969),
    1.4.1, p. 17, factorisation paragraph and first displayed isomorphism.
    In words: Every alternating m-linear map factors uniquely through the
    m-th exterior power, giving the isomorphism between forms and linear
    maps on that power. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alternating_word_component_multilinear m :
  multilinear (@alternating_word_component m).
Proof. exact: multilinear_words_power hb. Qed.

(** Source for [alternating_word_component_alternating]: Federer (1969),
    1.4.1, p. 17, factorisation paragraph and first displayed isomorphism.
    In words: Every alternating m-linear map factors uniquely through the
    m-th exterior power, giving the isomorphism between forms and linear
    maps on that power. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alternating_word_component_alternating m :
  alternating_power (@alternating_word_component m).
Proof. by move=> x hx; exact: ha. Qed.

(** Source for [alternating_word_sig]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition alternating_word_sig m :=
  boolp.cid (exterior_power_universal H (@alternating_word_component_multilinear m)
    (@alternating_word_component_alternating m)).

(** Source for [alternating_word_map]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition alternating_word_map m : {linear exterior_algebra V -> Z} :=
  proj1_sig (alternating_word_sig m).

(** Source for [exterior_word_extension_fun]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition exterior_word_extension_fun : E -> Z :=
  graded_sum (exterior_grading V) alternating_word_map.
HB.instance Definition _ := GRing.Linear.copy exterior_word_extension_fun
  (graded_sum (exterior_grading V) alternating_word_map).

(** Source for [exterior_word_extension]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition exterior_word_extension : {linear E -> Z} :=
  GRing.Linear.clone _ _ _ _ exterior_word_extension_fun _.

(** Source for [exterior_word_extensionE]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_word_extensionE s : exterior_word_extension (exterior_word s) = beta s.
Proof.
rewrite /= /exterior_word_extension_fun.
rewrite (graded_sum_homogeneous _ (exterior_word_homogeneous s)).
have := proj1 (proj2 (proj2_sig (alternating_word_sig (size s)))) (seq_power s).
by rewrite /algebra_power /alternating_word_component power_seqK.
Qed.
End AlternatingWords.

(** Federer 1.3.1, first paragraph: exterior degree zero is K and degree
    one is V. Both identifications are proved by explicit inverse maps. *)
(** Source for [word_degree_one_alternating]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma word_degree_one_alternating (s : seq V) : ~~ uniq s -> word_degree_one s = 0.
Proof. by case: s => [|v [|w s]]. Qed.

(** Source for [exterior_degree_one]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_degree_one : {linear E -> V} :=
  exterior_word_extension (@word_degree_one_multilinear K V) word_degree_one_alternating.

(** Source for [exterior_degree_one_word]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_degree_one_word s : exterior_degree_one (exterior_word s) = word_degree_one s.
Proof. exact: exterior_word_extensionE. Qed.

(** Source for [exterior_degree_one_projection]: Federer (1969), 1.3.1, p.
    13, quotient definition and exterior-multiplication paragraph. In words:
    The quotient by the square-generated ideal is the exterior algebra;
    products descend to wedge products, and the zeroth and first powers
    identify with R and V. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_degree_one_projection x :
  exterior_degree_one (exterior_projection V x) = tensor_degree_one V x.
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite exterior_projection_word exterior_degree_one_word tensor_degree_one_word.
Qed.

(** Source for [exterior_generatorK]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_generatorK : cancel (@exterior_generator K V) exterior_degree_one.
Proof. by move=> v; rewrite /exterior_generator exterior_degree_one_word. Qed.

(** Source for [exterior_generator_injective]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_generator_injective : injective (@exterior_generator K V).
Proof. exact: can_inj exterior_generatorK. Qed.

(** Source for [exterior_degree_one_reconstruction]: Federer (1969), 1.3.1,
    p. 13, quotient definition and exterior-multiplication paragraph. In
    words: The quotient by the square-generated ideal is the exterior
    algebra; products descend to wedge products, and the zeroth and first
    powers identify with R and V. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma exterior_degree_one_reconstruction x :
  exterior_degree 1 x = exterior_generator (exterior_degree_one x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite exterior_degree_word exterior_degree_one_word.
by case: s => [|v [|w s]] /=; rewrite /word_degree_one /= ?linear0.
Qed.

(** Source for [exterior_first_component]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_first_component x : homogeneous (exterior_grading V) 1 x ->
  exterior_generator (exterior_degree_one x) = x.
Proof. by move=> hx; rewrite -exterior_degree_one_reconstruction; exact: hx. Qed.

(** Source for [word_degree_zero_alternating]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma word_degree_zero_alternating (s : seq V) : ~~ uniq s -> word_degree_zero s = 0.
Proof. by case: s. Qed.

(** Source for [exterior_augmentation]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_augmentation : {linear E -> K^o} :=
  exterior_word_extension (@word_degree_zero_multilinear K V) word_degree_zero_alternating.

(** Source for [exterior_augmentation_word]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_augmentation_word s :
  exterior_augmentation (exterior_word s) = word_degree_zero s.
Proof. exact: exterior_word_extensionE. Qed.

(** Source for [exterior_augmentation_projection]: Federer (1969), 1.3.1, p.
    13, quotient definition and exterior-multiplication paragraph. In words:
    The quotient by the square-generated ideal is the exterior algebra;
    products descend to wedge products, and the zeroth and first powers
    identify with R and V. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_augmentation_projection x :
  exterior_augmentation (exterior_projection V x) = tensor_augmentation V x.
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite exterior_projection_word exterior_augmentation_word tensor_augmentation_word.
Qed.

(** Source for [exterior_augmentation_unit]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_augmentation_unit : exterior_augmentation (exterior_unit V) = 1.
Proof. exact: (exterior_augmentation_word [::]). Qed.

(** Source for [exterior_scalar]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_scalar (a : K^o) : E := (a : K) *: exterior_unit V.
(** Source for [exterior_scalar_linear]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_scalar_linear : linear exterior_scalar.
Proof. by move=> a b c; rewrite /exterior_scalar scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o E
  *:%R exterior_scalar exterior_scalar_linear.

(** Source for [exterior_scalarK]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_scalarK : cancel exterior_scalar exterior_augmentation.
Proof.
move=> a; rewrite /exterior_scalar linearZ exterior_augmentation_unit.
change ((a : K) * 1 = a); exact: mulr1.
Qed.

(** Source for [exterior_scalar_injective]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_scalar_injective : injective exterior_scalar.
Proof. exact: can_inj exterior_scalarK. Qed.

(** Source for [exterior_degree_zero_reconstruction]: Federer (1969), 1.3.1,
    p. 13, quotient definition and exterior-multiplication paragraph. In
    words: The quotient by the square-generated ideal is the exterior
    algebra; products descend to wedge products, and the zeroth and first
    powers identify with R and V. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma exterior_degree_zero_reconstruction x :
  exterior_degree 0 x = exterior_scalar (exterior_augmentation x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite exterior_degree_word exterior_augmentation_word /exterior_scalar.
by case: s => [|v s] /=; rewrite /word_degree_zero /= ?scale1r ?scale0r.
Qed.

(** Source for [exterior_zeroth_component]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_zeroth_component x : homogeneous (exterior_grading V) 0 x ->
  exterior_scalar (exterior_augmentation x) = x.
Proof. by move=> hx; rewrite -exterior_degree_zero_reconstruction; exact: hx. Qed.

(** Source for [exterior_unit_nonzero]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_unit_nonzero : exterior_unit V != 0.
Proof.
apply/eqP=> h; have e := exterior_augmentation_unit.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End ExteriorGrading.
Arguments exterior_degree {K V} n.
