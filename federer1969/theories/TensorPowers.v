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
  FamilyUpdate TensorFamilyUP WordEvaluation PowerWords TensorAlgebraUP
  TensorAlgebraSealed TensorAlgebra TensorGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** A multilinear function on words extends uniquely to a linear map on the
    tensor algebra. The extension is assembled degree by degree from the
    universal properties of the homogeneous components (Federer 1.2.3). *)
Section MultilinearWords.
Variable K : fieldType.
Variable V : lmodType K.
Variable Z : lmodType K.
Variable beta : seq V -> Z.
Hypothesis hb : multilinear_words beta.
Local Notation H := (tensor_algebraP V).

(** Source for [word_component]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_component m (x : {dffun forall i : 'I_m, power_family V m i}) : Z :=
  beta (power_seq x).

(** Source for [word_component_multilinear]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_component_multilinear m : multilinear (@word_component m).
Proof. exact: multilinear_words_power hb. Qed.

(** Source for [word_component_sig]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_component_sig m :=
  boolp.cid (power_universal H (@word_component_multilinear m)).

(** Source for [word_component_map]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_component_map m : {linear tensor_algebra V -> Z} :=
  proj1_sig (word_component_sig m).

(** Source for [multilinear_extension_fun]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Definition or construction used to
    formalise this passage. *)
Definition multilinear_extension_fun : tensor_algebra_space V -> Z :=
  graded_sum (tensor_grading V) word_component_map.
HB.instance Definition _ := GRing.Linear.copy multilinear_extension_fun
  (graded_sum (tensor_grading V) word_component_map).

(** Source for [multilinear_extension]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Definition or construction used to
    formalise this passage. *)
Definition multilinear_extension : {linear tensor_algebra_space V -> Z} :=
  GRing.Linear.clone _ _ _ _ multilinear_extension_fun _.

(** Source for [multilinear_extensionE]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_extensionE s : multilinear_extension (tensor_word s) = beta s.
Proof.
rewrite /= /multilinear_extension_fun.
rewrite (graded_sum_homogeneous _ (tensor_word_homogeneous s)).
have := proj1 (proj2 (proj2_sig (word_component_sig (size s)))) (seq_power s).
by rewrite /algebra_power /word_component power_seqK.
Qed.

(** Source for [multilinear_extension_unique]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_extension_unique (g : {linear tensor_algebra_space V -> Z}) :
  (forall s, g (tensor_word s) = beta s) -> forall x, g x = multilinear_extension x.
Proof.
move=> e; apply: tensor_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite e multilinear_extensionE.
Qed.

(** Source for [tensor_power_universal]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_power_universal n :
  (forall s, size s != n -> beta s = 0) ->
  exists g : {linear tensor_algebra_space V -> Z},
    (forall s, g (tensor_word s) = beta s) /\
    (forall x, g (tensor_degree n x) = g x) /\
    (forall h : {linear tensor_algebra_space V -> Z},
      (forall s, h (tensor_word s) = beta s) -> forall x, h x = g x).
Proof.
move=> hz; exists multilinear_extension; split.
  exact: multilinear_extensionE.
split; last exact: multilinear_extension_unique.
apply: tensor_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_degree_word; case hs: (size s == n) => //.
by rewrite linear0 multilinear_extensionE hz // hs.
Qed.
End MultilinearWords.

Section LowDegrees.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [word_degree_one]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_degree_one (s : seq V) : V :=
  if s is [:: v] then v else 0.

(** Source for [word_degree_one_multilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_degree_one_multilinear : multilinear_words word_degree_one.
Proof.
move=> s t a v w; case: s => [|u s].
  by case: t => [|r t] /=; rewrite /word_degree_one /= ?scaler0 ?add0r.
by case: s => [|r s] /=; rewrite /word_degree_one /= scaler0 add0r.
Qed.

(** Source for [tensor_degree_one]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_degree_one : {linear tensor_algebra_space V -> V} :=
  multilinear_extension word_degree_one_multilinear.

(** Source for [tensor_degree_one_word]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degree_one_word s : tensor_degree_one (tensor_word s) = word_degree_one s.
Proof. exact: multilinear_extensionE. Qed.

(** Source for [tensor_generatorK]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_generatorK : cancel (@tensor_generator K V) tensor_degree_one.
Proof. by move=> v; rewrite /tensor_generator tensor_degree_one_word. Qed.

(** Source for [tensor_generator_injective]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem tensor_generator_injective : injective (@tensor_generator K V).
Proof. exact: can_inj tensor_generatorK. Qed.

(** Source for [tensor_degree_one_reconstruction]: Federer (1969), 1.2.3, p.
    12, opening construction and multiplication paragraphs. In words: The
    tensor algebra is the direct sum of tensor powers, with degree zero
    equal to R and degree one equal to V; multiplication groups tensor
    factors, is associative, and has unit one. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_degree_one_reconstruction x :
  tensor_degree 1 x = tensor_generator (tensor_degree_one x).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_degree_word tensor_degree_one_word.
by case: s => [|v [|w s]] /=; rewrite /word_degree_one /= ?linear0.
Qed.

(** Source for [tensor_first_component]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_first_component x : homogeneous (tensor_grading V) 1 x ->
  tensor_generator (tensor_degree_one x) = x.
Proof. by move=> hx; rewrite -tensor_degree_one_reconstruction; exact: hx. Qed.

(** Source for [word_degree_zero]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_degree_zero (s : seq V) : K^o :=
  if s is [::] then 1 else 0.

(** Source for [word_degree_zero_multilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_degree_zero_multilinear : multilinear_words word_degree_zero.
Proof.
by move=> s t a v w; case: s => [|u s]; rewrite /word_degree_zero /= scaler0 add0r.
Qed.

(** Source for [tensor_augmentation]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_augmentation : {linear tensor_algebra_space V -> K^o} :=
  multilinear_extension word_degree_zero_multilinear.

(** Source for [tensor_augmentation_word]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_augmentation_word s : tensor_augmentation (tensor_word s) = word_degree_zero s.
Proof. exact: multilinear_extensionE. Qed.

(** Source for [tensor_augmentation_unit]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_augmentation_unit : tensor_augmentation (tensor_unit V) = 1.
Proof. exact: (tensor_augmentation_word [::]). Qed.

(** Source for [tensor_scalar]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_scalar (a : K^o) : tensor_algebra_space V :=
  (a : K) *: tensor_unit V.
(** Source for [tensor_scalar_linear]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_scalar_linear : linear tensor_scalar.
Proof. by move=> a b c; rewrite /tensor_scalar scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o (tensor_algebra_space V)
  *:%R tensor_scalar tensor_scalar_linear.

(** Source for [tensor_scalarK]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_scalarK : cancel tensor_scalar tensor_augmentation.
Proof.
move=> a; rewrite /tensor_scalar linearZ tensor_augmentation_unit.
change ((a : K) * 1 = a).
by rewrite mulr1.
Qed.

(** Source for [tensor_scalar_injective]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem tensor_scalar_injective : injective tensor_scalar.
Proof. exact: can_inj tensor_scalarK. Qed.

(** Source for [tensor_degree_zero_reconstruction]: Federer (1969), 1.2.3,
    p. 12, opening construction and multiplication paragraphs. In words: The
    tensor algebra is the direct sum of tensor powers, with degree zero
    equal to R and degree one equal to V; multiplication groups tensor
    factors, is associative, and has unit one. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_degree_zero_reconstruction x :
  tensor_degree 0 x = tensor_scalar (tensor_augmentation x).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_degree_word tensor_augmentation_word /tensor_scalar.
by case: s => [|v s] /=; rewrite /word_degree_zero /= ?scale1r ?scale0r.
Qed.

(** Source for [tensor_zeroth_component]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_zeroth_component x : homogeneous (tensor_grading V) 0 x ->
  tensor_scalar (tensor_augmentation x) = x.
Proof. by move=> hx; rewrite -tensor_degree_zero_reconstruction; exact: hx. Qed.

(** Source for [tensor_unit_nonzero]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem tensor_unit_nonzero : tensor_unit V != 0.
Proof.
apply/eqP=> h; have e := tensor_augmentation_unit.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End LowDegrees.
