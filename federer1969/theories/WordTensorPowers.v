(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector ModuleQuotient Bilinear
  AlgebraUP WordEvaluation WordAlgebra WordTensorAlgebra GradedAlgebra
  WordTensorGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The homogeneous components have the multilinear universal property.
    A map on words of length n is represented by its zero extension to all
    finite words. Linearity in each position is expressed using word contexts. *)
Section MultilinearWords.
Variable K : fieldType.
Variable V : lmodType K.
Variable Z : lmodType K.
Variable beta : seq V -> Z.

Hypothesis hb : multilinear_words beta.

(** Source for [multilinear_free]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition multilinear_free : {linear word_space K (Choice.clone V _) -> Z} :=
  GRing.Linear.clone _ _ _ _ (free_extend beta) _.

(** Source for [multilinear_relation_killed]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_relation_killed x : word_relation x -> multilinear_free x = 0.
Proof.
elim=> [|x' y hx ihx hy ihy|a x' hx ihx|s t v w|s t a v].
- exact: linear0.
- by rewrite linearD /= ihx ihy add0r.
- by rewrite linearZ /= ihx scaler0.
- rewrite linearB linearD /= /multilinear_free /= !free_extend_delta.
  by rewrite (linD (hb s t)) subrr.
- rewrite linearB linearZ /= /multilinear_free /= !free_extend_delta.
  by rewrite (linZ (hb s t)) subrr.
Qed.

(** Source for [multilinear_extension]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Definition or construction used to
    formalise this passage. *)
Definition multilinear_extension : {linear tensor_algebra_space V -> Z} :=
  GRing.Linear.clone _ _ _ _
    (quotient_lift (S := word_subspace V) (f := multilinear_free)
      multilinear_relation_killed) _.

(** Source for [multilinear_extensionE]: Federer (1969), 1.2.3, p. 12,
    definition of the m-th tensor power as the tensor product of m copies of
    V. In words: The degree-m component is the m-fold tensor product of V.
    By its universal property in 1.1.1, p. 9, an m-linear map factors
    uniquely through this component. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_extensionE s : multilinear_extension (tensor_word s) = beta s.
Proof.
change (quotient_lift (S := word_subspace V) (f := multilinear_free)
  multilinear_relation_killed
  (quotient_projection (word_subspace V) (word_delta K s)) = beta s).
rewrite quotient_liftE; exact: free_extend_delta.
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
