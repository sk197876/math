(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP WordEvaluation
  TensorAlgebra GradedAlgebra TensorGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section GradedExtension.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Hypothesis hmul : graded_product G (alg_mul A).
Hypothesis hone : homogeneous G 0 (alg_one A).
Variable f : {linear V -> A}.
Hypothesis hf : forall v, homogeneous G 1 (f v).

(** Source for [word_eval_homogeneous]: Federer (1969), 1.2.3, p. 12,
    universal mapping property in the last two paragraphs. In words: Every
    linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma word_eval_homogeneous s : homogeneous G (size s) (word_eval f s).
Proof.
elim: s => [|v s ih] /=; first exact: hone.
have h := hmul (hf v) ih.
by rewrite add1n in h.
Qed.

(** Source for [tensor_extension_component]: Federer (1969), 1.2.3, p. 12,
    universal mapping property in the last two paragraphs. In words: Every
    linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma tensor_extension_component n x :
  homogeneous G n (tensor_algebra_extension f (tensor_degree n x)).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- rewrite !linear0; exact: homogeneous0.
- rewrite !linearD; exact: homogeneousD hx hy.
- rewrite !linearZ; exact: homogeneousZ hx.
rewrite tensor_degree_word; case hs: (size s == n).
  move/eqP: hs => <-.
  rewrite tensor_algebra_extension_word.
  exact: word_eval_homogeneous.
rewrite linear0; exact: homogeneous0.
Qed.

(** Source for [tensor_algebra_extension_graded]: Federer (1969), 1.2.3, p.
    12, universal mapping property in the last two paragraphs. In words:
    Every linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Supporting lemma for this passage; not separately stated
    in the book. *)
Theorem tensor_algebra_extension_graded :
  preserves_grading (tensor_grading V) G (tensor_algebra_extension f).
Proof.
move=> n x hx; rewrite -hx; exact: tensor_extension_component.
Qed.

(** Source for [graded_tensor_algebra_universal]: Federer (1969), 1.2.3, p.
    12, universal mapping property in the last two paragraphs. In words:
    Every linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem graded_tensor_algebra_universal :
  exists g : algebra_map (tensor_algebra V) A,
    (forall v, g (tensor_generator v) = f v) /\
    preserves_grading (tensor_grading V) G g /\
    (forall h : algebra_map (tensor_algebra V) A,
      (forall v, h (tensor_generator v) = f v) -> forall x, h x = g x).
Proof.
exists (tensor_algebra_extension f); split.
  exact: tensor_algebra_extension_generator.
split; first exact: tensor_algebra_extension_graded.
exact: tensor_algebra_extension_unique.
Qed.
End GradedExtension.

Section InducedMap.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.

(** Source for [tensor_algebra_map]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Definition or construction used
    to formalise this passage. *)
Definition tensor_algebra_map : algebra_map (tensor_algebra V) (tensor_algebra W) :=
  tensor_algebra_extension (A := tensor_algebra W)
    (linear_comp (GRing.Linear.clone _ _ _ _ (tensor_generator (V := W)) _) f).

(** Source for [tensor_algebra_mapE]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_mapE v :
  tensor_algebra_map (tensor_generator v) = tensor_generator (f v).
Proof. exact: tensor_algebra_extension_generator. Qed.

(** Source for [tensor_algebra_map_word]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_map_word s :
  tensor_algebra_map (tensor_word s) = tensor_word [seq f v | v <- s].
Proof.
elim: s => [|v s ih]; first exact: (algebra_map_one tensor_algebra_map).
rewrite -[v :: s]/([:: v] ++ s) -tensor_product_words.
change (tensor_algebra_map
  (alg_mul (tensor_algebra V) (tensor_generator v) (tensor_word s)) =
  tensor_word (f v :: [seq f v' | v' <- s])).
rewrite algebra_map_mul tensor_algebra_mapE ih.
exact: tensor_product_words.
Qed.

(** Source for [tensor_algebra_map_graded]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_map_graded :
  preserves_grading (tensor_grading V) (tensor_grading W) tensor_algebra_map.
Proof.
rewrite /tensor_algebra_map.
apply: (@tensor_algebra_extension_graded K V (tensor_algebra W) (tensor_grading W)).
- exact (@tensor_product_graded K W).
- exact: (tensor_unit_homogeneous W).
by move=> v; exact: tensor_generator_homogeneous.
Qed.
End InducedMap.

Section FunctorLaws.
Variable K : fieldType.
Variables V W Z : lmodType K.

(** Source for [tensor_algebra_map_id]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_map_id x : tensor_algebra_map (linear_id V) x = x.
Proof.
apply: (tensor_algebra_ext (@tensor_algebra_exists K V)
  (tensor_algebra_map (linear_id V)) (algebra_id (tensor_algebra V))) x.
by move=> v; rewrite tensor_algebra_mapE.
Qed.

(** Source for [tensor_algebra_map_comp]: Federer (1969), 1.2.3, p. 13,
    naturality paragraph before the heading of section 1.3. In words: A
    linear map induces a unique unit-preserving tensor-algebra map; this map
    is the direct sum of its tensor powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma tensor_algebra_map_comp (f : {linear V -> W}) (g : {linear W -> Z}) x :
  tensor_algebra_map g (tensor_algebra_map f x) =
  tensor_algebra_map (linear_comp g f) x.
Proof.
apply: (tensor_algebra_ext (@tensor_algebra_exists K V)
  (algebra_comp (tensor_algebra_map g) (tensor_algebra_map f))
  (tensor_algebra_map (linear_comp g f))) x.
change (forall v, tensor_algebra_map g
  (tensor_algebra_map f (tensor_generator v)) =
  tensor_algebra_map (linear_comp g f) (tensor_generator v)).
by move=> v; rewrite !tensor_algebra_mapE.
Qed.
End FunctorLaws.
