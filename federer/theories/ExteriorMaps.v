(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP WordAlgebra
  GradedAlgebra GradedComponents GradedUnit TensorAlgebra TensorAlgebraMaps
  ExteriorUP ExteriorAlgebra ExteriorGrading ExteriorAnticommutativity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1, universal mapping property. In the target algebra the
    unit has degree zero by 1.2.1; it is not an additional hypothesis. *)
Section GradedExtension.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Hypothesis hmul : graded_product G (alg_mul A).
Variable f : {linear V -> A}.
Hypothesis hf : forall v, homogeneous G 1 (f v).
Hypothesis hs : forall v, alg_mul A (f v) (f v) = 0.

(** Source for [exterior_extension_component]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma exterior_extension_component n x :
  homogeneous G n (exterior_algebra_extension hs (exterior_degree n x)).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- rewrite !linear0; exact: homogeneous0.
- rewrite !linearD; exact: homogeneousD hx hy.
- rewrite !linearZ; exact: homogeneousZ hx.
rewrite exterior_degree_word; case hsz: (size s == n).
  move/eqP: hsz => <-; rewrite exterior_algebra_extension_word.
  apply: (@word_eval_homogeneous K V A G hmul) => //.
  exact: (@graded_unit_degree_zero K A G (alg_mul A) (alg_bilinear A)
    hmul (alg_one A) (@alg_unitl K A) (@alg_unitr K A)).
rewrite linear0; exact: homogeneous0.
Qed.

(** Source for [exterior_algebra_extension_graded]: Federer (1969), 1.3.1,
    p. 14, universal mapping property and its proof. In words: Linear maps
    into degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma exterior_algebra_extension_graded :
  preserves_grading (exterior_grading V) G (exterior_algebra_extension hs).
Proof. by move=> n x hx; rewrite -hx; exact: exterior_extension_component. Qed.
End GradedExtension.

Section FedererUniversalProperty.
Variable K : fieldType.
Hypothesis characteristic_not_two : (1 + 1 : K) != 0.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Hypotheses (hmul : graded_product G (alg_mul A))
  (hanti : graded_anticommutative G (alg_mul A)).
Variable f : {linear V -> A}.
Hypothesis hf : forall v, homogeneous G 1 (f v).

(** Federer 1.3.1, existence proof: anticommutativity and characteristic
    different from two imply that every element of A_1 has square zero. *)
(** Source for [exterior_target_square_zero]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma exterior_target_square_zero v : alg_mul A (f v) (f v) = 0.
Proof.
exact: (@degree_one_square_zero K A G (alg_mul A)
  hanti characteristic_not_two (f v) (hf v)).
Qed.

(** Source for [graded_exterior_algebra_universal]: Federer (1969), 1.3.1,
    p. 14, universal mapping property and its proof. In words: Linear maps
    into degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem graded_exterior_algebra_universal :
  exists g : algebra_map (exterior_algebra V) A,
    (forall v, g (exterior_generator v) = f v) /\
    preserves_grading (exterior_grading V) G g /\
    (forall h : algebra_map (exterior_algebra V) A,
      (forall v, h (exterior_generator v) = f v) -> forall x, h x = g x).
Proof.
exists (exterior_algebra_extension exterior_target_square_zero); split.
  exact: exterior_algebra_extension_generator.
split.
  exact: (@exterior_algebra_extension_graded K V A G hmul f hf
    exterior_target_square_zero).
exact: exterior_algebra_extension_unique.
Qed.
End FedererUniversalProperty.

(** Source for [graded_exterior_algebra_exists]: Federer (1969), 1.3.1, p.
    14, universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem graded_exterior_algebra_exists (K : fieldType)
    (h2 : (1 + 1 : K) != 0) (V : lmodType K) :
  @is_graded_exterior_algebra K V (exterior_algebra V) (exterior_grading V)
    (GRing.Linear.clone _ _ _ _ (@exterior_generator K V) _).
Proof.
move=> A G hm hc f hf.
have [g [ge [gg gu]]] := @graded_exterior_algebra_universal K h2 V A G hm hc f hf.
exists g; split=> //; split=> //.
by move=> h he _; exact: gu he.
Qed.

(** Federer 1.3.1, last paragraph: the induced map wedge* f and its
    restrictions wedge^m f. These natural maps exist in every characteristic. *)
Section InducedMap.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.

(** Source for [exterior_generator_map]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Definition
    or construction used to formalise this passage. *)
Definition exterior_generator_map : {linear V -> exterior_space W} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (@exterior_generator K W) _) f.
(** Source for [exterior_generator_map_square]: Federer (1969), 1.3.1, p.
    14, final naturality paragraph. In words: A linear map extends uniquely
    to a unit-preserving exterior-algebra homomorphism, which is the direct
    sum of the induced maps on exterior powers. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_generator_map_square v :
  alg_mul (exterior_algebra W) (exterior_generator_map v) (exterior_generator_map v) = 0.
Proof. exact: exterior_generator_square. Qed.

(** Source for [exterior_algebra_map]: Federer (1969), 1.3.1, p. 14, final
    naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Definition or construction used
    to formalise this passage. *)
Definition exterior_algebra_map : algebra_map (exterior_algebra V) (exterior_algebra W) :=
  exterior_algebra_extension exterior_generator_map_square.

(** Source for [exterior_algebra_mapE]: Federer (1969), 1.3.1, p. 14, final
    naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_mapE v :
  exterior_algebra_map (exterior_generator v) = exterior_generator (f v).
Proof. exact: exterior_algebra_extension_generator. Qed.

(** Source for [exterior_algebra_map_word]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_algebra_map_word s :
  exterior_algebra_map (exterior_word s) = exterior_word [seq f v | v <- s].
Proof.
elim: s => [|v s ih]; first exact: (algebra_map_one exterior_algebra_map).
rewrite exterior_word_cons.
change (exterior_algebra_map
  (alg_mul (exterior_algebra V) (exterior_generator v) (exterior_word s)) =
  exterior_word (f v :: [seq f v' | v' <- s])).
by rewrite algebra_map_mul exterior_algebra_mapE ih exterior_word_cons.
Qed.

(** Source for [exterior_algebra_map_unique]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_map_unique (g : algebra_map (exterior_algebra V) (exterior_algebra W)) :
  (forall v, g (exterior_generator v) = exterior_generator (f v)) ->
  forall x, g x = exterior_algebra_map x.
Proof.
move=> hg; exact: (@exterior_algebra_extension_unique K V (exterior_algebra W)
  exterior_generator_map exterior_generator_map_square g hg).
Qed.

(** Source for [exterior_algebra_map_graded]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_algebra_map_graded :
  preserves_grading (exterior_grading V) (exterior_grading W) exterior_algebra_map.
Proof.
apply: (@exterior_algebra_extension_graded K V (exterior_algebra W)
  (exterior_grading W) (@wedge_graded K W)).
by move=> v; exact: exterior_generator_homogeneous.
Qed.

(** Source for [exterior_power_map]: Federer (1969), 1.3.1, p. 14, final
    naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Definition or construction used
    to formalise this passage. *)
Definition exterior_power_map n : {linear exterior_power V n -> exterior_power W n} :=
  GRing.Linear.clone _ _ _ _ (component_map (n := n) exterior_algebra_map_graded) _.

(** Source for [exterior_algebra_map_degree]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_map_degree n x :
  exterior_degree n (exterior_algebra_map x) = exterior_algebra_map (exterior_degree n x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD -hx -hy.
- by rewrite !linearZ hx.
rewrite exterior_algebra_map_word !exterior_degree_word size_map.
by case: ifP => _; rewrite ?linear0 ?exterior_algebra_map_word.
Qed.

(** Source for [exterior_algebra_map_direct_sum]: Federer (1969), 1.3.1, p.
    14, final naturality paragraph. In words: A linear map extends uniquely
    to a unit-preserving exterior-algebra homomorphism, which is the direct
    sum of the induced maps on exterior powers. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_map_direct_sum x :
  exists N, exterior_algebra_map x =
    \sum_(i < N) component_val (exterior_power_map i (component (exterior_grading V) i x)).
Proof.
have [N hN] := exterior_degree_finite x; exists N.
rewrite {1}hN linear_sum; apply: eq_bigr => i _; by [].
Qed.
End InducedMap.

Section FunctorLaws.
Variable K : fieldType.
Variables V W Z : lmodType K.

(** Source for [exterior_algebra_map_id]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_map_id x : exterior_algebra_map (linear_id V) x = x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (exterior_algebra_map (linear_id V)) (algebra_id (exterior_algebra V))) x.
by move=> v; rewrite exterior_algebra_mapE.
Qed.

(** Source for [exterior_algebra_map_eq]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_algebra_map_eq (f g : {linear V -> W}) :
  (forall v, f v = g v) -> forall x, exterior_algebra_map f x = exterior_algebra_map g x.
Proof.
move=> e; apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (exterior_algebra_map f) (exterior_algebra_map g)).
by move=> v; rewrite !exterior_algebra_mapE e.
Qed.

(** Source for [exterior_algebra_map_comp]: Federer (1969), 1.3.1, p. 14,
    final naturality paragraph. In words: A linear map extends uniquely to a
    unit-preserving exterior-algebra homomorphism, which is the direct sum
    of the induced maps on exterior powers. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_algebra_map_comp (f : {linear V -> W}) (g : {linear W -> Z}) x :
  exterior_algebra_map g (exterior_algebra_map f x) =
  exterior_algebra_map (linear_comp g f) x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp (exterior_algebra_map g) (exterior_algebra_map f))
  (exterior_algebra_map (linear_comp g f))) x.
change (forall v, exterior_algebra_map g
  (exterior_algebra_map f (exterior_generator v)) =
  exterior_algebra_map (linear_comp g f) (exterior_generator v)).
by move=> v; rewrite !exterior_algebra_mapE.
Qed.
End FunctorLaws.
