(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear AlgebraUP GradedAlgebra GradedComponents
  GradedUnit GradedStructure GradedTensorUP TensorAlgebra TensorGrading TensorPowers
  TensorAlgebraMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3: tensor powers as actual homogeneous component spaces. *)
(** Source for [tensor_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_power (K : fieldType) (V : lmodType K) n :=
  graded_component (tensor_grading V) n.

Section LowPowers.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (tensor_algebra_space V).
Local Notation G := (tensor_grading V).

(** Source for [tensor_zeroth_inclusion]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_zeroth_inclusion : {linear K^o -> tensor_power V 0} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 0) _)
    (GRing.Linear.clone _ _ _ _ (tensor_scalar V) _).
(** Source for [tensor_zeroth_inverse]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_zeroth_inverse : {linear tensor_power V 0 -> K^o} :=
  linear_comp (tensor_augmentation V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 0) _).
(** Source for [tensor_zeroth_inclusionK]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_zeroth_inclusionK : cancel tensor_zeroth_inclusion tensor_zeroth_inverse.
Proof.
move=> a; change (tensor_augmentation V (tensor_degree 0 (tensor_scalar V a)) = a).
have h : homogeneous G 0 (tensor_scalar V a).
  exact: (@homogeneousZ K E G 0 a (tensor_unit V) (tensor_unit_homogeneous V)).
by rewrite h tensor_scalarK.
Qed.
(** Source for [tensor_zeroth_inverseK]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_zeroth_inverseK : cancel tensor_zeroth_inverse tensor_zeroth_inclusion.
Proof.
move=> x; apply/val_inj.
change (tensor_degree 0 (tensor_scalar V (tensor_augmentation V (component_val x))) =
  component_val x).
rewrite -tensor_degree_zero_reconstruction tensor_degree_orthogonal eqxx.
exact: (component_homogeneous x).
Qed.

(** Source for [tensor_first_inclusion]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_first_inclusion : {linear V -> tensor_power V 1} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (component G 1) _)
    (GRing.Linear.clone _ _ _ _ (@tensor_generator K V) _).
(** Source for [tensor_first_inverse]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_first_inverse : {linear tensor_power V 1 -> V} :=
  linear_comp (tensor_degree_one V)
    (GRing.Linear.clone _ _ _ _ (@component_val K E G 1) _).
(** Source for [tensor_first_inclusionK]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_first_inclusionK : cancel tensor_first_inclusion tensor_first_inverse.
Proof.
move=> v; change (tensor_degree_one V (tensor_degree 1 (tensor_generator v)) = v).
by rewrite (tensor_generator_homogeneous v) tensor_generatorK.
Qed.
(** Source for [tensor_first_inverseK]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_first_inverseK : cancel tensor_first_inverse tensor_first_inclusion.
Proof.
move=> x; apply/val_inj.
change (tensor_degree 1 (tensor_generator (tensor_degree_one V (component_val x))) =
  component_val x).
rewrite -tensor_degree_one_reconstruction tensor_degree_orthogonal eqxx.
exact: (component_homogeneous x).
Qed.
(** Source for [tensor_zeroth_inclusionE]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_zeroth_inclusionE a :
  component_val (tensor_zeroth_inclusion a) = tensor_scalar V a.
Proof.
exact: (@homogeneousZ K E G 0 a (tensor_unit V) (tensor_unit_homogeneous V)).
Qed.
(** Source for [tensor_first_inclusionE]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_first_inclusionE v :
  component_val (tensor_first_inclusion v) = tensor_generator v.
Proof. exact: tensor_generator_homogeneous. Qed.
(** Source for [tensor_scalar_unit_grading]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem tensor_scalar_unit_grading :
  @scalar_unit_grading K (tensor_algebra V) (tensor_grading V).
Proof.
split; first exact: tensor_unit_nonzero.
move=> x hx; exists (tensor_augmentation V x).
exact: esym (tensor_zeroth_component hx).
Qed.
End LowPowers.


Section ComponentWords.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.

(** Source for [tensor_power_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_word (s : seq V) : tensor_power V n :=
  component (tensor_grading V) n (tensor_word s).
(** Source for [tensor_power_wordE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_wordE s : component_val (tensor_power_word s) =
  if size s == n then tensor_word s else 0.
Proof. exact: tensor_degree_word. Qed.

(** Source for [tensor_word_multilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_word_multilinear : multilinear_words (@tensor_word K V).
Proof.
move=> s t a v w.
have hw u : tensor_word (s ++ u :: t) = tensor_product (tensor_word s)
    (tensor_product (tensor_generator u) (tensor_word t)).
  by rewrite /tensor_generator !tensor_product_words.
rewrite !hw.
by rewrite tensor_generator_linear (bilDl (tensor_product_bilinear V))
  (bilZl (tensor_product_bilinear V)) (bilDr (tensor_product_bilinear V))
  (bilZr (tensor_product_bilinear V)).
Qed.

(** Source for [tensor_power_word_multilinear]: Federer (1969), 1.2.3, p.
    12, definition of the m-th tensor power as the tensor product of m
    copies of V. In words: The degree-m component is the m-fold tensor
    product of V. By its universal property in 1.1.1, p. 9, an m-linear map
    factors uniquely through this component. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma tensor_power_word_multilinear : multilinear_words tensor_power_word.
Proof.
by move=> s t a v w; rewrite /tensor_power_word tensor_word_multilinear linearP.
Qed.

(** Source for [tensor_power_word_wrong]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_word_wrong s : size s != n -> tensor_power_word s = 0.
Proof.
move=> hs; apply/val_inj.
change (component_val (tensor_power_word s) = component_val (0 : tensor_power V n)).
by rewrite tensor_power_wordE (negPf hs) linear0.
Qed.

(** Source for [tensor_power_induction]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_induction (P : tensor_power V n -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, size s = n -> P (tensor_power_word s)) : forall x, P x.
Proof.
move=> x; rewrite -[x]componentK.
elim/tensor_word_induction: (component_val x) => [|y z hy hz|a y hy|s].
- by rewrite linear0.
- rewrite linearD; exact: hD.
- rewrite linearZ; exact: hZ.
case hs: (size s == n); first exact: hw (elimT eqP hs).
change (P (tensor_power_word s)); by rewrite tensor_power_word_wrong ?hs //.
Qed.

Variable Z : lmodType K.
Variable beta : seq V -> Z.
Hypothesis hb : multilinear_words beta.
Hypothesis hz : forall s, size s != n -> beta s = 0.

(** Source for [tensor_power_extension]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_extension : {linear tensor_power V n -> Z} :=
  linear_comp (multilinear_extension hb)
    (GRing.Linear.clone _ _ _ _ (@component_val K _ (tensor_grading V) n) _).
(** Source for [tensor_power_extensionE]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_extensionE s : tensor_power_extension (tensor_power_word s) = beta s.
Proof.
change (multilinear_extension hb (component_val (tensor_power_word s)) = beta s).
rewrite tensor_power_wordE; case hs: (size s == n).
- exact: multilinear_extensionE.
- by rewrite linear0 hz // hs.
Qed.

(** Source for [tensor_power_component_universal]: Federer (1969), 1.2.3, p.
    12, definition of the m-th tensor power as the tensor product of m
    copies of V. In words: The degree-m component is the m-fold tensor
    product of V. By its universal property in 1.1.1, p. 9, an m-linear map
    factors uniquely through this component. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem tensor_power_component_universal :
  exists g : {linear tensor_power V n -> Z},
    (forall s, g (tensor_power_word s) = beta s) /\
    (forall h : {linear tensor_power V n -> Z},
      (forall s, h (tensor_power_word s) = beta s) -> forall x, h x = g x).
Proof.
exists tensor_power_extension; split; first exact: tensor_power_extensionE.
move=> h he; apply: tensor_power_induction => [|x y hx hy|a x hx|s hs].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- by rewrite he tensor_power_extensionE.
Qed.
End ComponentWords.

Section InducedPowers.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.
(** Source for [tensor_power_map]: Federer (1969), 1.2.3, p. 13, naturality
    paragraph before the heading of section 1.3. In words: A linear map
    induces a unique unit-preserving tensor-algebra map; this map is the
    direct sum of its tensor powers. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_map n : {linear tensor_power V n -> tensor_power W n} :=
  GRing.Linear.clone _ _ _ _ (component_map (n := n) (tensor_algebra_map_graded f)) _.
(** Source for [tensor_algebra_map_degree]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_map_degree n x :
  tensor_degree n (tensor_algebra_map f x) = tensor_algebra_map f (tensor_degree n x).
Proof.
exact: (@graded_map_projection K _ _ (tensor_grading V) (tensor_grading W)
  (tensor_algebra_map f) (tensor_algebra_map_graded f) n x).
Qed.
(** Source for [tensor_power_map_word]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_power_map_word n s :
  tensor_power_map n (tensor_power_word n s) = tensor_power_word n [seq f v | v <- s].
Proof.
apply/val_inj; change (tensor_algebra_map f (tensor_degree n (tensor_word s)) =
  tensor_degree n (tensor_word [seq f v | v <- s])).
by rewrite -tensor_algebra_map_degree tensor_algebra_map_word.
Qed.
(** Source for [tensor_algebra_map_direct_sum]: Federer (1969), 1.2.3, p.
    13, naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem tensor_algebra_map_direct_sum x :
  exists N, tensor_algebra_map f x =
    \sum_(i < N) component_val (tensor_power_map i (component (tensor_grading V) i x)).
Proof.
have [N hN] := tensor_degree_finite x; exists N.
rewrite {1}hN linear_sum; apply: eq_bigr => i _; by [].
Qed.
End InducedPowers.

(** The unit-degree condition in the older extension theorem is derived,
    not added to Federer's hypotheses. *)
(** Source for [graded_tensor_algebra_exists]: Federer (1969), 1.2.3, p. 12,
    universal mapping property in the last two paragraphs. In words: Every
    linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem graded_tensor_algebra_exists (K : fieldType) (V : lmodType K) :
  @is_graded_tensor_algebra K V (tensor_algebra V) (tensor_grading V)
    (GRing.Linear.clone _ _ _ _ (@tensor_generator K V) _).
Proof.
move=> A G hm f hf.
have h1 := @graded_unit_degree_zero K A G (alg_mul A) (alg_bilinear A)
  hm (alg_one A) (@alg_unitl K A) (@alg_unitr K A).
have [g [ge [gg gu]]] := @graded_tensor_algebra_universal K V A G hm h1 f hf.
exists g; split=> //; split=> //.
by move=> h he _; exact: gu he.
Qed.
