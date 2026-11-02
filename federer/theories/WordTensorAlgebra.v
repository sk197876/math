(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap generic_quotient.
From Federer Require Import TensorUP TensorMaps FreeVector ModuleQuotient
  Bilinear AlgebraUP WordEvaluation WordAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3. The linearity relations are inserted in arbitrary word
    contexts, so their linear span is a two-sided ideal. *)
Section TensorAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation X := (Choice.clone V _).
Local Notation F := (word_space K X).
Local Notation d := (word_delta K (X := X)).
Local Notation wb := (word_bilinear K X).

(** Source for [word_relation]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Inductive word_relation : F -> Prop :=
| wr_zero : word_relation 0
| wr_add x y : word_relation x -> word_relation y -> word_relation (x + y)
| wr_scale a x : word_relation x -> word_relation (a *: x)
| wr_linear_add s t v w :
    word_relation (d (s ++ (v + w) :: t) -
      (d (s ++ v :: t) + d (s ++ w :: t)))
| wr_linear_scale s t a v :
    word_relation (d (s ++ (a *: v) :: t) - a *: d (s ++ v :: t)).

(** Source for [word_subspace]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_subspace : subspace F :=
  @Subspace K F word_relation wr_zero wr_add wr_scale.

(** Source for [word_relation_prefix]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_prefix s x : word_relation x -> word_relation (word_mul (d s) x).
Proof.
elim=> [|x' y hx ihx hy ihy|a x' hx ihx|u t v w|u t a v].
- by rewrite (bil0r wb); exact: wr_zero.
- rewrite (bilDr wb); exact: wr_add ihx ihy.
- rewrite (bilZr wb); exact: wr_scale ihx.
- rewrite (bilBr wb) (bilDr wb) !word_mulE !catA.
  exact: wr_linear_add.
- rewrite (bilBr wb) (bilZr wb) !word_mulE !catA.
  exact: wr_linear_scale.
Qed.

(** Source for [word_relation_suffix]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_suffix s x : word_relation x -> word_relation (word_mul x (d s)).
Proof.
elim=> [|x' y hx ihx hy ihy|a x' hx ihx|u t v w|u t a v].
- by rewrite (bil0l wb); exact: wr_zero.
- rewrite (bilDl wb); exact: wr_add ihx ihy.
- rewrite (bilZl wb); exact: wr_scale ihx.
- rewrite (bilBl wb) (bilDl wb) !word_mulE -!catA /=.
  exact: wr_linear_add.
- rewrite (bilBl wb) (bilZl wb) !word_mulE -!catA /=.
  exact: wr_linear_scale.
Qed.

(** Source for [word_relation_mull]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_mull x y : word_relation y -> word_relation (word_mul x y).
Proof.
move=> hy; elim/free_induction: x => [|x x' hx hx'|a x hx|s].
- by rewrite (bil0l wb); exact: wr_zero.
- rewrite (bilDl wb); exact: wr_add hx hx'.
- rewrite (bilZl wb); exact: wr_scale hx.
exact: word_relation_prefix hy.
Qed.

(** Source for [word_relation_mulr]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_mulr x y : word_relation x -> word_relation (word_mul x y).
Proof.
move=> hx; elim/free_induction: y => [|y y' hy hy'|a y hy|s].
- by rewrite (bil0r wb); exact: wr_zero.
- rewrite (bilDr wb); exact: wr_add hy hy'.
- rewrite (bilZr wb); exact: wr_scale hy.
exact: word_relation_suffix hx.
Qed.

(** Source for [tensor_algebra_space]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_algebra_space := module_quotient word_subspace.
HB.instance Definition _ := GRing.Lmodule.copy tensor_algebra_space
  (module_quotient word_subspace).
Local Notation pi := (quotient_projection word_subspace).

(** Source for [tensor_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_word s : tensor_algebra_space := pi (d s).
(** Source for [tensor_unit]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_unit := tensor_word [::].
(** Source for [tensor_generator]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_generator v := tensor_word [:: v].

(** Source for [tensor_generatorD]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generatorD v w :
  tensor_generator (v + w) = tensor_generator v + tensor_generator w.
Proof.
rewrite /tensor_generator /tensor_word -linearD /=.
apply/quotient_projection_eq; exact: (wr_linear_add [::] [::] v w).
Qed.
(** Source for [tensor_generatorZ]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generatorZ a v : tensor_generator (a *: v) = a *: tensor_generator v.
Proof.
rewrite /tensor_generator /tensor_word -linearZ /=.
apply/quotient_projection_eq; exact: (wr_linear_scale [::] [::] a v).
Qed.
(** Source for [tensor_generator_linear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generator_linear : linear tensor_generator.
Proof. by move=> a v w; rewrite tensor_generatorD tensor_generatorZ. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V tensor_algebra_space
  *:%R tensor_generator tensor_generator_linear.

(** Source for [word_product_compatible]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_product_compatible x y x' y' :
  pi x = pi x' -> pi y = pi y' -> pi (word_mul x y) = pi (word_mul x' y').
Proof.
move/quotient_projection_eq=> hx; move/quotient_projection_eq=> hy.
apply: eq_trans (_ : pi (word_mul x' y) = _).
  apply/quotient_projection_eq; rewrite -(bilBl wb).
  exact: word_relation_mulr hx.
apply/quotient_projection_eq; rewrite -(bilBr wb).
exact: word_relation_mull hy.
Qed.

(** Source for [tensor_product]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_product (x y : tensor_algebra_space) :=
  pi (word_mul (repr x) (repr y)).

(** Source for [tensor_productE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_productE x y : tensor_product (pi x) (pi y) = pi (word_mul x y).
Proof. apply: word_product_compatible; exact: quotient_projection_surjective. Qed.

(** Source for [tensor_product_words]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_words s t : tensor_product (tensor_word s) (tensor_word t) =
  tensor_word (s ++ t).
Proof. by rewrite /tensor_word tensor_productE word_mulE. Qed.

(** Source for [tensor_product_bilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_bilinear : bilinear tensor_product.
Proof.
split=> [y a x x'|x a y y'].
  rewrite -[x]quotient_projection_surjective -[x']quotient_projection_surjective
    -[y]quotient_projection_surjective -linearP !tensor_productE.
  by rewrite (bilDl wb) (bilZl wb) linearP.
rewrite -[x]quotient_projection_surjective -[y]quotient_projection_surjective
  -[y']quotient_projection_surjective -linearP !tensor_productE.
by rewrite (bilDr wb) (bilZr wb) linearP.
Qed.

(** Source for [tensor_product_assoc]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_assoc : associative tensor_product.
Proof.
move=> x y z; rewrite -[x]quotient_projection_surjective
  -[y]quotient_projection_surjective -[z]quotient_projection_surjective.
by rewrite !tensor_productE word_assoc.
Qed.
(** Source for [tensor_product_unitl]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_unitl : left_id tensor_unit tensor_product.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
by rewrite /tensor_unit /tensor_word tensor_productE word_unitl quotient_projection_surjective.
Qed.
(** Source for [tensor_product_unitr]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_unitr : right_id tensor_unit tensor_product.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
by rewrite /tensor_unit /tensor_word tensor_productE word_unitr quotient_projection_surjective.
Qed.

(** Source for [tensor_algebra]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_algebra : algebra K :=
  @Algebra K (GRing.Lmodule.clone K tensor_algebra_space _) tensor_product tensor_unit
    tensor_product_bilinear tensor_product_assoc tensor_product_unitl tensor_product_unitr.

(** Source for [tensor_word_induction]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_word_induction (P : tensor_algebra_space -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, P (tensor_word s)) : forall x, P x.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
elim/free_induction: (repr x) => [|u v hu hv|a u hu|s].
- by rewrite linear0.
- rewrite linearD; exact: hD hu hv.
- rewrite linearZ; exact: hZ hu.
exact: hw.
Qed.

Section Extension.
Variable A : algebra K.
Variable f : {linear V -> A}.

(** Source for [word_relation_killed]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_killed x : word_relation x -> word_extend f x = 0.
Proof.
elim=> [|x' y hx ihx hy ihy|a x' hx ihx|s t v w|s t a v].
- exact: linear0.
- by rewrite linearD /= ihx ihy add0r.
- by rewrite linearZ /= ihx scaler0.
- rewrite linearB linearD /= !word_extendE !word_eval_cat /= linearD.
  by rewrite (bilDl (alg_bilinear A)) (bilDr (alg_bilinear A)) subrr.
- rewrite linearB linearZ /= !word_extendE !word_eval_cat /= linearZ.
  by rewrite (bilZl (alg_bilinear A)) (bilZr (alg_bilinear A)) subrr.
Qed.

(** Source for [tensor_algebra_lift]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Definition or
    construction used to formalise this passage. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Definition tensor_algebra_lift : tensor_algebra_space -> A :=
  quotient_lift (S := word_subspace) (f := word_extend f) word_relation_killed.
HB.instance Definition _ := GRing.Linear.copy tensor_algebra_lift
  (quotient_lift (S := word_subspace) (f := word_extend f) word_relation_killed).

(** Source for [tensor_algebra_liftE]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Supporting lemma for
    this passage; not separately stated in the book. The ungraded universal
    property is a local strengthening; it is not the literal graded property
    stated in this passage. *)
Lemma tensor_algebra_liftE s : tensor_algebra_lift (tensor_word s) = word_eval f s.
Proof. by rewrite /tensor_algebra_lift /tensor_word quotient_liftE word_extendE. Qed.

(** Source for [tensor_algebra_lift_one]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_lift_one : tensor_algebra_lift tensor_unit = alg_one A.
Proof. exact: tensor_algebra_liftE. Qed.

(** Source for [tensor_algebra_lift_mul]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_lift_mul x y :
  tensor_algebra_lift (tensor_product x y) =
  alg_mul A (tensor_algebra_lift x) (tensor_algebra_lift y).
Proof.
rewrite -[x]quotient_projection_surjective -[y]quotient_projection_surjective.
by rewrite tensor_productE /tensor_algebra_lift !quotient_liftE word_extend_mul.
Qed.

(** Source for [tensor_algebra_extension]: Federer (1969), 1.2.3, p. 12,
    graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Definition or construction used to formalise this passage. The ungraded
    universal property is a local strengthening; it is not the literal
    graded property stated in this passage. *)
Definition tensor_algebra_extension : algebra_map tensor_algebra A :=
  @AlgebraMap K tensor_algebra A
    (GRing.Linear.clone _ _ _ _ tensor_algebra_lift _)
    tensor_algebra_lift_one tensor_algebra_lift_mul.

(** Source for [tensor_algebra_extension_word]: Federer (1969), 1.2.3, p.
    12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_extension_word s :
  tensor_algebra_extension (tensor_word s) = word_eval f s.
Proof. exact: tensor_algebra_liftE. Qed.

(** Source for [tensor_algebra_extension_generator]: Federer (1969), 1.2.3,
    p. 12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Supporting lemma for this passage; not separately stated in the book.
    The ungraded universal property is a local strengthening; it is not the
    literal graded property stated in this passage. *)
Lemma tensor_algebra_extension_generator v :
  tensor_algebra_extension (tensor_generator v) = f v.
Proof. by rewrite /tensor_algebra_extension /= tensor_algebra_liftE /= alg_unitr. Qed.

(** Source for [tensor_algebra_extension_unique]: Federer (1969), 1.2.3, p.
    12, graded universal-property paragraph (context for the ungraded
    extension). In words: Federer states unique unit-preserving extension
    for a linear map into degree one of a graded target. The construction
    here also provides extension to ungraded associative unital targets.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. The ungraded universal property is a local
    strengthening; it is not the literal graded property stated in this
    passage. *)
Lemma tensor_algebra_extension_unique (g : algebra_map tensor_algebra A) :
  (forall v, g (tensor_generator v) = f v) ->
  forall x, g x = tensor_algebra_extension x.
Proof.
move=> e; apply: tensor_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD /= hx hy.
- by rewrite !linearZ /= hx.
rewrite /tensor_algebra_extension /= tensor_algebra_liftE.
elim: s => [|v s ih]; first exact: (algebra_map_one g).
rewrite -[v :: s]/([:: v] ++ s) -tensor_product_words.
change (g (alg_mul tensor_algebra (tensor_generator v) (tensor_word s)) =
  alg_mul A (f v) (word_eval f s)).
by rewrite algebra_map_mul e ih.
Qed.
End Extension.

(** Source for [tensor_algebra_exists]: Federer (1969), 1.2.3, p. 12, graded
    universal-property paragraph (context for the ungraded extension). In
    words: Federer states unique unit-preserving extension for a linear map
    into degree one of a graded target. The construction here also provides
    extension to ungraded associative unital targets. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The ungraded universal property is a local strengthening; it is
    not the literal graded property stated in this passage. *)
Theorem tensor_algebra_exists :
  @is_tensor_algebra K V tensor_algebra
    (GRing.Linear.clone _ _ _ _ tensor_generator _).
Proof.
move=> A f; exists (tensor_algebra_extension f); split.
  exact: tensor_algebra_extension_generator.
exact: tensor_algebra_extension_unique.
Qed.
End TensorAlgebra.
