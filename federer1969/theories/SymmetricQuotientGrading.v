(** Federer (1969), 1.9.1, p. 41: grading of the symmetric quotient, private
    existence machinery. The full algebra starts in degree zero; the
    displayed lower index 2 in the book is a printing error, contradicted by
    its next sentence. This is a local correction, absent from the saved
    erratum. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP
  GradedAlgebra GradedComponents TensorAlgebra TensorGrading TensorPowers
  AlgebraQuotient SymmetricIdeal SymmetricQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation pi := (quotient_projection (commutator_ideal V)).

(** Source for [symmetric_grading]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting construction
    for this passage, in words: The grading induced by word length, starting
    in degree zero. *)
Definition symmetric_grading : grading E :=
  @quotient_grading K (tensor_algebra V) (commutator_ideal V) (tensor_grading V)
    (@commutator_ideal_homogeneous K V).

(** Source for [symmetric_degree]: Federer 1.9.1, p. 41, homogeneous powers,
    spanning and low-degree identifications. Supporting construction for
    this passage, in words: Projection to a specified homogeneous degree. *)
Definition symmetric_degree n : {linear E -> E} := grade symmetric_grading n.

(** Source for [symmetric_power]: Federer 1.9.1, p. 41, homogeneous powers,
    spanning and low-degree identifications. Supporting construction for
    this passage, in words: The homogeneous component of a specified degree. *)
Definition symmetric_power n := graded_component symmetric_grading n.
HB.instance Definition _ n := GRing.Lmodule.copy (symmetric_power n)
  (graded_component symmetric_grading n).

(** Source for [symmetric_degree_projection]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: Taking a homogeneous component
    commutes with the tensor projection. *)
Lemma symmetric_degree_projection n x : symmetric_degree n (pi x) = pi (tensor_degree n x).
Proof. exact: quotient_gradeE. Qed.

(** Source for [symmetric_degree_word]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting construction
    for this passage, in words: The degree-n projection retains a word of
    length n and kills words of other lengths. *)
Lemma symmetric_degree_word n s :
  symmetric_degree n (symmetric_word s) = if size s == n then symmetric_word s else 0.
Proof.
rewrite /symmetric_word symmetric_degree_projection tensor_degree_word.
by case: ifP => _; rewrite ?linear0.
Qed.

(** Source for [symmetric_degree_orthogonal]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: Homogeneous projections are
    idempotent and mutually orthogonal. *)
Lemma symmetric_degree_orthogonal m n x :
  symmetric_degree m (symmetric_degree n x) = if m == n then symmetric_degree n x else 0.
Proof. exact: grade_orthogonal. Qed.

(** Source for [symmetric_degree_finite]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting construction
    for this passage, in words: Each element is the finite sum of its
    homogeneous components, including degree zero. *)
Lemma symmetric_degree_finite x : exists N, x = \sum_(i < N) symmetric_degree i x.
Proof. exact: grade_finite. Qed.

(** Source for [symmetric_word_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: A word has homogeneous degree
    equal to its number of factors. *)
Lemma symmetric_word_homogeneous s :
  homogeneous symmetric_grading (size s) (symmetric_word s).
Proof. by rewrite /homogeneous -/(symmetric_degree _ _) symmetric_degree_word eqxx. Qed.

(** Source for [symmetric_unit_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: The unit has degree zero. *)
Lemma symmetric_unit_homogeneous : homogeneous symmetric_grading 0 (symmetric_unit V).
Proof. exact: (symmetric_word_homogeneous [::]). Qed.

(** Source for [symmetric_generator_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: Every generator has degree one. *)
Lemma symmetric_generator_homogeneous v :
  homogeneous symmetric_grading 1 (symmetric_generator v).
Proof. exact: (symmetric_word_homogeneous [:: v]). Qed.

(** Source for [symmetric_projection_graded]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: The tensor projection preserves
    homogeneous degree. *)
Lemma symmetric_projection_graded :
  preserves_grading (tensor_grading V) symmetric_grading pi.
Proof.
exact: (@quotient_projection_graded K (tensor_algebra V) (commutator_ideal V)
  (tensor_grading V) (@commutator_ideal_homogeneous K V)).
Qed.

(** Source for [symmetric_product_graded]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting construction
    for this passage, in words: Multiplication adds homogeneous degrees. *)
Lemma symmetric_product_graded : graded_product symmetric_grading (@symmetric_product K V).
Proof.
exact: (@quotient_mul_graded K (tensor_algebra V) (commutator_ideal V) (tensor_grading V)
  (@commutator_ideal_homogeneous K V) (@tensor_product_graded K V)).
Qed.

(** Source for [graded_symmetric_algebra]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting construction
    for this passage, in words: The symmetric algebra with its homogeneous
    grading and graded multiplication. *)
Definition graded_symmetric_algebra : graded_algebra K :=
  @GradedAlgebra K E symmetric_grading (@symmetric_product K V) (symmetric_product_bilinear V) symmetric_product_graded.

(** Source for [symmetric_component_induction]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    construction for this passage, in words: Words of length n span the
    degree-n component and give its induction principle. *)
Lemma symmetric_component_induction n (P : E -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, size s = n -> P (symmetric_word s)) :
    forall x, homogeneous symmetric_grading n x -> P x.
Proof.
have hp : forall x, P (symmetric_degree n x).
  apply: symmetric_word_induction => [|x y hx hy|a x hx|s].
  - by rewrite linear0.
  - rewrite linearD; exact: hD hx hy.
  - rewrite linearZ; exact: hZ hx.
  rewrite symmetric_degree_word; case: ifP => [/eqP hs|_]; last exact: h0.
  exact: hw hs.
by move=> x hx; rewrite -hx; exact: hp.
Qed.

End SymmetricGrading.
Arguments symmetric_degree {K V} n.
