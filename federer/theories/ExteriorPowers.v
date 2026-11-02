(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP
  GradedAlgebra GradedComponents WordEvaluation TensorAlgebra TensorGrading
  AlgebraQuotient SquareZeroWords ExteriorIdeal ExteriorAlgebraUP ExteriorSealed
  ExteriorAlgebra ExteriorGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1, first paragraph: the kernel of the canonical
    homomorphism of the tensor algebra onto the exterior algebra is mV. The
    inclusion of mV follows from the square relation; the converse uses the
    universal property to map the exterior algebra into the quotient algebra
    of the tensor algebra by mV. *)
Section Kernel.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation T := (tensor_algebra V).
Local Notation q := (quotient_algebra_projection (mV V)).

(** Source for [exterior_projection_killed]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_projection_killed x : mV V x -> exterior_projection V x = 0.
Proof. exact: (exterior_relation_killed (exterior_square (exterior_algebraP V))). Qed.

(** Source for [quotient_generator]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition quotient_generator : {linear V -> quotient_algebra (mV V)} :=
  linear_comp q (GRing.Linear.clone _ _ _ _ (@tensor_generator K V) _).

(** Source for [quotient_generator_square]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma quotient_generator_square v :
  alg_mul (quotient_algebra (mV V)) (quotient_generator v) (quotient_generator v) = 0.
Proof.
change (alg_mul (quotient_algebra (mV V)) (q (tensor_generator v)) (q (tensor_generator v))
  = 0).
rewrite -algebra_map_mul; apply/ideal_projection_zero.
exact: mV_square.
Qed.

(** Source for [exterior_projection_quotient]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_projection_quotient x :
  exterior_algebra_extension quotient_generator_square (exterior_projection V x) = q x.
Proof.
rewrite exterior_algebra_extension_projection.
by symmetry; apply: tensor_algebra_extension_unique.
Qed.

(** Source for [exterior_projection_kernel]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem exterior_projection_kernel x : exterior_projection V x = 0 <-> mV V x.
Proof.
split; last exact: exterior_projection_killed.
move=> hx; apply/ideal_projection_zero.
by rewrite -[quotient_projection _ x]/(q x) -exterior_projection_quotient hx linear0.
Qed.

(** Source for [tensor_word_nonuniq_mV]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma tensor_word_nonuniq_mV s : ~~ uniq s -> mV V (tensor_word s).
Proof.
move=> hs; apply/exterior_projection_kernel.
rewrite exterior_projection_word /exterior_word.
exact: (square_zero_word_nonuniq (exterior_square (exterior_algebraP V)) hs).
Qed.
End Kernel.

(** Federer 1.3.1, first paragraph: wedge^m V is the quotient of tensor^m V
    by its intersection with mV. The maps below exhibit this isomorphism
    between actual vector spaces, including both inverse equations. *)
Section PowerQuotient.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Local Notation T := (tensor_algebra_space V).
Local Notation E := (exterior_space V).
Local Notation Tn := (graded_component (tensor_grading V) n).
Local Notation En := (exterior_power V n).
Local Notation pi := (exterior_projection V).

(** Source for [exterior_power_rel]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_power_rel (x : Tn) := mV V (component_val x).
(** Source for [exterior_power_rel0]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_power_rel0 : exterior_power_rel 0.
Proof. rewrite /exterior_power_rel linear0; exact: subspace_zero. Qed.
(** Source for [exterior_power_relD]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_power_relD x y :
  exterior_power_rel x -> exterior_power_rel y -> exterior_power_rel (x + y).
Proof. by move=> hx hy; rewrite /exterior_power_rel linearD; exact: subspace_add hx hy. Qed.
(** Source for [exterior_power_relZ]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_power_relZ a x : exterior_power_rel x -> exterior_power_rel (a *: x).
Proof. by move=> hx; rewrite /exterior_power_rel linearZ; exact: subspace_scale hx. Qed.

(** Source for [exterior_power_subspace]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_power_subspace : subspace Tn :=
  @Subspace K Tn exterior_power_rel exterior_power_rel0
    exterior_power_relD exterior_power_relZ.
Local Notation Qn := (module_quotient exterior_power_subspace).
Local Notation pin := (quotient_projection exterior_power_subspace).

(** Source for [exterior_power_projection]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_power_projection : {linear Tn -> En} :=
  GRing.Linear.clone _ _ _ _ (component_map (n := n) (@exterior_projection_graded K V)) _.
(** Source for [exterior_power_projectionE]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_power_projectionE x :
  component_val (exterior_power_projection x) = pi (component_val x).
Proof. by []. Qed.
(** Source for [exterior_power_projection_killed]: Federer (1969), 1.3.1, p.
    13, quotient definition and exterior-multiplication paragraph. In words:
    The quotient by the square-generated ideal is the exterior algebra;
    products descend to wedge products, and the zeroth and first powers
    identify with R and V. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_power_projection_killed x :
  exterior_power_subspace x -> exterior_power_projection x = 0.
Proof.
move=> hx; apply/val_inj.
change (pi (component_val x) = component_val (0 : En)).
rewrite linear0; exact: exterior_projection_killed hx.
Qed.

(** Source for [exterior_power_quotient]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_power_quotient : {linear Qn -> En} := GRing.Linear.clone _ _ _ _
  (quotient_lift (f := exterior_power_projection) exterior_power_projection_killed) _.
(** Source for [exterior_power_quotientE]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_power_quotientE x :
  exterior_power_quotient (pin x) = exterior_power_projection x.
Proof. exact: quotient_liftE. Qed.

(** Source for [exterior_power_word]: Federer (1969), 1.3.1, p. 13, quotient
    definition and exterior-multiplication paragraph. In words: The quotient
    by the square-generated ideal is the exterior algebra; products descend
    to wedge products, and the zeroth and first powers identify with R and
    V. Definition or construction used to formalise this passage. *)
Definition exterior_power_word (s : seq V) : Qn :=
  pin (component (tensor_grading V) n (tensor_word s)).

(** Source for [exterior_power_word_multilinear]: Federer (1969), 1.4.1, p.
    17, factorisation paragraph and first displayed isomorphism. In words:
    Every alternating m-linear map factors uniquely through the m-th
    exterior power, giving the isomorphism between forms and linear maps on
    that power. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma exterior_power_word_multilinear : multilinear_words exterior_power_word.
Proof.
move=> s t a v w; rewrite /exterior_power_word.
by rewrite [tensor_word _](word_eval_multilinear (tensor_generator_map V)) !linearP.
Qed.

(** Source for [exterior_power_word_alternating]: Federer (1969), 1.4.1, p.
    17, factorisation paragraph and first displayed isomorphism. In words:
    Every alternating m-linear map factors uniquely through the m-th
    exterior power, giving the isomorphism between forms and linear maps on
    that power. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma exterior_power_word_alternating s : ~~ uniq s -> exterior_power_word s = 0.
Proof.
move=> hs; rewrite /exterior_power_word -(linear0 pin).
apply/quotient_projection_eq; rewrite subr0.
change (mV V (component_val (component (tensor_grading V) n (tensor_word s)))).
rewrite componentE; apply: mV_homogeneous.
exact: tensor_word_nonuniq_mV.
Qed.

(** Source for [exterior_power_inverse_aux]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_power_inverse_aux : {linear E -> Qn} :=
  exterior_word_extension exterior_power_word_multilinear
    exterior_power_word_alternating.

(** Source for [exterior_power_inverse_auxE]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_power_inverse_auxE x :
  exterior_power_inverse_aux (pi x) = pin (component (tensor_grading V) n x).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite exterior_projection_word exterior_word_extensionE.
Qed.

(** Source for [exterior_power_inverse]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_power_inverse : {linear En -> Qn} :=
  linear_comp exterior_power_inverse_aux
    (GRing.Linear.clone _ _ _ _ (@component_val K E (exterior_grading V) n) _).

(** Source for [exterior_power_quotientK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_power_quotientK : cancel exterior_power_quotient exterior_power_inverse.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective exterior_power_quotientE.
change (exterior_power_inverse_aux (pi (component_val (repr x))) = pin (repr x)).
by rewrite exterior_power_inverse_auxE componentK.
Qed.

(** Source for [exterior_power_inverse_degree]: Federer (1969), 1.3.1, p.
    13, quotient definition and exterior-multiplication paragraph. In words:
    The quotient by the square-generated ideal is the exterior algebra;
    products descend to wedge products, and the zeroth and first powers
    identify with R and V. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_power_inverse_degree y :
  component_val (exterior_power_quotient (exterior_power_inverse_aux y)) =
  exterior_degree n y.
Proof.
elim/exterior_word_induction: y => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD -hx -hy.
- by rewrite !linearZ -hx.
rewrite exterior_word_extensionE /exterior_power_word exterior_power_quotientE.
rewrite exterior_power_projectionE componentE.
change (pi (tensor_degree n (tensor_word s)) = exterior_degree n (exterior_word s)).
rewrite tensor_degree_word exterior_degree_word.
by case: ifP => _; rewrite ?exterior_projection_word ?linear0.
Qed.

(** Source for [exterior_power_inverseK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_power_inverseK : cancel exterior_power_inverse exterior_power_quotient.
Proof.
move=> x; apply/val_inj.
change (component_val (exterior_power_quotient
  (exterior_power_inverse_aux (component_val x))) = component_val x).
rewrite exterior_power_inverse_degree.
exact: component_homogeneous.
Qed.

(** Source for [exterior_power_is_quotient]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem exterior_power_is_quotient :
  exists (f : {linear Qn -> En}) (g : {linear En -> Qn}),
    cancel f g /\ cancel g f /\
    (forall x, component_val (f (pin x)) = pi (component_val x)).
Proof.
exists exterior_power_quotient, exterior_power_inverse; split.
  exact: exterior_power_quotientK.
split; first exact: exterior_power_inverseK.
by move=> x; rewrite exterior_power_quotientE exterior_power_projectionE.
Qed.
End PowerQuotient.

(** Federer 1.3.1, first paragraph: the displayed identifications of the
    zeroth and first powers, now as inverse linear maps of component spaces. *)
Section LowPowers.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).

(** Source for [exterior_zeroth_inclusion]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_zeroth_inclusion : {linear K^o -> exterior_power V 0} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 0) _)
    (GRing.Linear.clone _ _ _ _ (exterior_scalar V) _).
(** Source for [exterior_zeroth_inverse]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_zeroth_inverse : {linear exterior_power V 0 -> K^o} :=
  linear_comp (exterior_augmentation V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 0) _).
(** Source for [exterior_zeroth_inclusionK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_zeroth_inclusionK : cancel exterior_zeroth_inclusion exterior_zeroth_inverse.
Proof.
move=> a; change (exterior_augmentation V (exterior_degree 0 (exterior_scalar V a)) = a).
have h : homogeneous G 0 (exterior_scalar V a).
  exact: (@homogeneousZ K E G 0 a (exterior_unit V) (exterior_unit_homogeneous V)).
by rewrite h exterior_scalarK.
Qed.
(** Source for [exterior_zeroth_inverseK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_zeroth_inverseK : cancel exterior_zeroth_inverse exterior_zeroth_inclusion.
Proof.
move=> x; apply/val_inj.
change (exterior_degree 0 (exterior_scalar V (exterior_augmentation V (component_val x))) =
  component_val x).
rewrite -exterior_degree_zero_reconstruction exterior_degree_orthogonal eqxx.
exact: component_homogeneous.
Qed.

(** Source for [exterior_first_inclusion]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_first_inclusion : {linear V -> exterior_power V 1} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 1) _)
    (GRing.Linear.clone _ _ _ _ (@exterior_generator K V) _).
(** Source for [exterior_first_inverse]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Definition or construction used to formalise this passage. *)
Definition exterior_first_inverse : {linear exterior_power V 1 -> V} :=
  linear_comp (exterior_degree_one V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 1) _).
(** Source for [exterior_first_inclusionK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_first_inclusionK : cancel exterior_first_inclusion exterior_first_inverse.
Proof.
move=> v; change (exterior_degree_one V (exterior_degree 1 (exterior_generator v)) = v).
by rewrite (exterior_generator_homogeneous v) exterior_generatorK.
Qed.
(** Source for [exterior_first_inverseK]: Federer (1969), 1.3.1, p. 13,
    quotient definition and exterior-multiplication paragraph. In words: The
    quotient by the square-generated ideal is the exterior algebra; products
    descend to wedge products, and the zeroth and first powers identify with
    R and V. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_first_inverseK : cancel exterior_first_inverse exterior_first_inclusion.
Proof.
move=> x; apply/val_inj.
change (exterior_degree 1 (exterior_generator (exterior_degree_one V (component_val x))) =
  component_val x).
rewrite -exterior_degree_one_reconstruction exterior_degree_orthogonal eqxx.
exact: component_homogeneous.
Qed.
End LowPowers.

(** Federer 1.3.1 notation. These localisable notations keep wedge products
    and wedge powers distinct from logical conjunction and natural powers. *)
Declare Scope federer_exterior_scope.
Delimit Scope federer_exterior_scope with exterior.
Notation "'⋀*' V" := (exterior_space V)
  (at level 35, V at level 34) : federer_exterior_scope.
Notation "'⋀^' m V" := (exterior_power V m)
  (at level 35, m at level 0, V at level 34) : federer_exterior_scope.
Infix "∧" := wedge (at level 40, left associativity) : federer_exterior_scope.
