(** Federer (1969), 1.9.1, pp. 41-42: graded extension, induced maps and
    their degree components. All proofs use only the public sealed algebra
    and its universal property. Arbitrary fields replace the sources' real
    scalars. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP WordAlgebra
  GradedAlgebra GradedComponents GradedUnit TensorAlgebra TensorAlgebraMaps
  SymmetricUP SymmetricAlgebra SymmetricGrading GradedSymmetricUP.

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
Variable f : {linear V -> A}.
Hypothesis hf : forall v, homogeneous G 1 (f v).
Hypothesis hs : commutative (alg_mul A).

(** Source for [symmetric_extension_component]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The extension of a degree-one
    generator map preserves each homogeneous component. *)
Lemma symmetric_extension_component n x :
  homogeneous G n (symmetric_algebra_extension f hs (symmetric_degree n x)).
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- rewrite !linear0; exact: homogeneous0.
- rewrite !linearD; exact: homogeneousD hx hy.
- rewrite !linearZ; exact: homogeneousZ hx.
rewrite symmetric_degree_word; case hsz: (size s == n).
  move/eqP: hsz => <-; rewrite symmetric_algebra_extension_word.
  apply: (@word_eval_homogeneous K V A G hmul) => //.
  exact: (@graded_unit_degree_zero K A G (alg_mul A) (alg_bilinear A)
    hmul (alg_one A) (@alg_unitl K A) (@alg_unitr K A)).
rewrite linear0; exact: homogeneous0.
Qed.

(** Source for [symmetric_algebra_extension_graded]: Federer 1.9.1, pp.
    41-42, graded extension and induced-map paragraphs. Supporting
    definition or lemma for this passage, in words: The algebra extension
    preserves the grading. *)
Lemma symmetric_algebra_extension_graded :
  preserves_grading (symmetric_grading V) G (symmetric_algebra_extension f hs).
Proof. by move=> n x hx; rewrite -hx; exact: symmetric_extension_component. Qed.
End GradedExtension.

Section FedererUniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Hypotheses (hmul : graded_product G (alg_mul A))
  (hc : commutative (alg_mul A)).
Variable f : {linear V -> A}.
Hypothesis hf : forall v, homogeneous G 1 (f v).

(** Source for [graded_symmetric_algebra_universal]: Federer 1.9.1, pp.
    41-42, graded extension and induced-map paragraphs. Supporting
    definition or lemma for this passage, in words: Every degree-one linear
    map to a commutative graded target extends uniquely to a graded unital
    algebra map. *)
Theorem graded_symmetric_algebra_universal :
  exists g : algebra_map (symmetric_algebra V) A,
    (forall v, g (symmetric_generator v) = f v) /\
    preserves_grading (symmetric_grading V) G g /\
    (forall h : algebra_map (symmetric_algebra V) A,
      (forall v, h (symmetric_generator v) = f v) -> forall x, h x = g x).
Proof.
exists (symmetric_algebra_extension f hc); split.
  exact: symmetric_algebra_extension_generator.
split.
  exact: (@symmetric_algebra_extension_graded K V A G hmul f hf
    hc).
exact: symmetric_algebra_extension_unique.
Qed.
End FedererUniversalProperty.

(** Source for [graded_symmetric_algebra_exists]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The sealed algebra satisfies the
    independent graded universal-property specification. *)
Theorem graded_symmetric_algebra_exists (K : fieldType)
    (V : lmodType K) :
  @is_graded_symmetric_algebra K V (symmetric_algebra V) (symmetric_grading V)
    (GRing.Linear.clone _ _ _ _ (@symmetric_generator K V) _).
Proof.
move=> A G hc hm f hf.
have [g [ge [gg gu]]] := @graded_symmetric_algebra_universal K V A G hm hc f hf.
exists g; split=> //; split=> //.
by move=> h he _; exact: gu he.
Qed.

Section InducedMap.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.

(** Source for [symmetric_generator_map]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: Compose a given linear map with insertion into
    the target symmetric algebra. *)
Definition symmetric_generator_map : {linear V -> symmetric_space W} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (@symmetric_generator K W) _) f.

(** Source for [symmetric_algebra_map]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: The induced algebra map extending a linear map
    between vector spaces. *)
Definition symmetric_algebra_map : algebra_map (symmetric_algebra V) (symmetric_algebra W) :=
  symmetric_algebra_extension symmetric_generator_map (@symmetric_product_commute K W).

(** Source for [symmetric_algebra_mapE]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: The induced map sends the generator of v to the
    generator of f(v). *)
Lemma symmetric_algebra_mapE v :
  symmetric_algebra_map (symmetric_generator v) = symmetric_generator (f v).
Proof. exact: symmetric_algebra_extension_generator. Qed.

(** Source for [symmetric_algebra_map_word]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The induced map applies the original
    linear map to every factor of a word. *)
Lemma symmetric_algebra_map_word s :
  symmetric_algebra_map (symmetric_word s) = symmetric_word [seq f v | v <- s].
Proof.
elim: s => [|v s ih]; first exact: (algebra_map_one symmetric_algebra_map).
rewrite symmetric_word_cons.
change (symmetric_algebra_map
  (alg_mul (symmetric_algebra V) (symmetric_generator v) (symmetric_word s)) =
  symmetric_word (f v :: [seq f v' | v' <- s])).
by rewrite algebra_map_mul symmetric_algebra_mapE ih symmetric_word_cons.
Qed.

(** Source for [symmetric_algebra_map_unique]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The induced map is the unique algebra
    map with the required generator values. *)
Lemma symmetric_algebra_map_unique (g : algebra_map (symmetric_algebra V) (symmetric_algebra W)) :
  (forall v, g (symmetric_generator v) = symmetric_generator (f v)) ->
  forall x, g x = symmetric_algebra_map x.
Proof.
move=> hg; exact: (@symmetric_algebra_extension_unique K V (symmetric_algebra W)
  symmetric_generator_map (@symmetric_product_commute K W) g hg).
Qed.

(** Source for [symmetric_algebra_map_graded]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The induced algebra map preserves
    every homogeneous degree. *)
Lemma symmetric_algebra_map_graded :
  preserves_grading (symmetric_grading V) (symmetric_grading W) symmetric_algebra_map.
Proof.
apply: (@symmetric_algebra_extension_graded K V (symmetric_algebra W)
  (symmetric_grading W) (@symmetric_product_graded K W)).
by move=> v; exact: symmetric_generator_homogeneous.
Qed.

(** Source for [symmetric_power_map]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: The restriction of the induced algebra map to
    the degree-n symmetric power. *)
Definition symmetric_power_map n : {linear symmetric_power V n -> symmetric_power W n} :=
  GRing.Linear.clone _ _ _ _ (component_map (n := n) symmetric_algebra_map_graded) _.

(** Source for [symmetric_algebra_map_degree]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The induced map commutes with
    homogeneous projection. *)
Lemma symmetric_algebra_map_degree n x :
  symmetric_degree n (symmetric_algebra_map x) = symmetric_algebra_map (symmetric_degree n x).
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD -hx -hy.
- by rewrite !linearZ hx.
rewrite symmetric_algebra_map_word !symmetric_degree_word size_map.
by case: ifP => _; rewrite ?linear0 ?symmetric_algebra_map_word.
Qed.

(** Source for [symmetric_algebra_map_direct_sum]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: The induced algebra map is the direct
    sum of its homogeneous-power maps. *)
Lemma symmetric_algebra_map_direct_sum x :
  exists N, symmetric_algebra_map x =
    \sum_(i < N) component_val (symmetric_power_map i (component (symmetric_grading V) i x)).
Proof.
have [N hN] := symmetric_degree_finite x; exists N.
rewrite {1}hN linear_sum; apply: eq_bigr => i _; by [].
Qed.
End InducedMap.

Section FunctorLaws.
Variable K : fieldType.
Variables V W Z : lmodType K.

(** Source for [symmetric_algebra_map_id]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: The identity linear map induces the identity
    algebra map. *)
Lemma symmetric_algebra_map_id x : symmetric_algebra_map (linear_id V) x = x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K V)
  (symmetric_algebra_map (linear_id V)) (algebra_id (symmetric_algebra V))) x.
by move=> v; rewrite symmetric_algebra_mapE.
Qed.

(** Source for [symmetric_algebra_map_eq]: Federer 1.9.1, pp. 41-42, graded
    extension and induced-map paragraphs. Supporting definition or lemma for
    this passage, in words: Pointwise equal linear maps induce pointwise
    equal algebra maps. *)
Lemma symmetric_algebra_map_eq (f g : {linear V -> W}) :
  (forall v, f v = g v) -> forall x, symmetric_algebra_map f x = symmetric_algebra_map g x.
Proof.
move=> e; apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K W)
  (symmetric_algebra_map f) (symmetric_algebra_map g)).
by move=> v; rewrite !symmetric_algebra_mapE e.
Qed.

(** Source for [symmetric_algebra_map_comp]: Federer 1.9.1, pp. 41-42,
    graded extension and induced-map paragraphs. Supporting definition or
    lemma for this passage, in words: Inducing an algebra map commutes with
    composition of linear maps. *)
Lemma symmetric_algebra_map_comp (f : {linear V -> W}) (g : {linear W -> Z}) x :
  symmetric_algebra_map g (symmetric_algebra_map f x) =
  symmetric_algebra_map (linear_comp g f) x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K Z)
  (algebra_comp (symmetric_algebra_map g) (symmetric_algebra_map f))
  (symmetric_algebra_map (linear_comp g f))) x.
change (forall v, symmetric_algebra_map g
  (symmetric_algebra_map f (symmetric_generator v)) =
  symmetric_algebra_map (linear_comp g f) (symmetric_generator v)).
by move=> v; rewrite !symmetric_algebra_mapE.
Qed.
End FunctorLaws.
