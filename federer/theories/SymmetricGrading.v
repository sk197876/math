(** Federer (1969), 1.9.1, p. 41: public homogeneous powers, word spanning,
    and identifications of degrees zero and one. The symmetric algebra sum
    starts at zero; the printed lower index 2 is a local correction, as
    explained in SymmetricQuotientGrading.v. No private construction is
    imported here. Arbitrary fields are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require boolp.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedSums
  GradedComponents FamilyUpdate TensorFamilyUP WordEvaluation PowerWords
  TensorAlgebraUP TensorAlgebra TensorGrading TensorPowers SymmetricAlgebraUP SymmetricSealed SymmetricAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation H := (symmetric_algebraP V).

(** Source for [symmetric_degree]: Federer 1.9.1, p. 41, homogeneous powers,
    spanning and low-degree identifications. Supporting definition or lemma
    for this passage, in words: Projection to a specified homogeneous
    degree. *)
Definition symmetric_degree n : {linear E -> E} := grade (symmetric_grading V) n.

(** Source for [symmetric_power]: Federer 1.9.1, p. 41, homogeneous powers,
    spanning and low-degree identifications. Supporting definition or lemma
    for this passage, in words: The homogeneous component of a specified
    degree. *)
Definition symmetric_power n := graded_component (symmetric_grading V) n.
HB.instance Definition _ n := GRing.Lmodule.copy (symmetric_power n)
  (graded_component (symmetric_grading V) n).

(** Source for [symmetric_word_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: A word has homogeneous
    degree equal to its number of factors. *)
Lemma symmetric_word_homogeneous s :
  homogeneous (symmetric_grading V) (size s) (symmetric_word s).
Proof. exact: sym_word_homogeneous H s. Qed.

(** Source for [symmetric_degree_word]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The degree-n projection retains a
    word of length n and kills words of other lengths. *)
Lemma symmetric_degree_word n s :
  symmetric_degree n (symmetric_word s) = if size s == n then symmetric_word s else 0.
Proof.
rewrite /symmetric_degree (grade_homogeneous _ (symmetric_word_homogeneous s)).
by rewrite eq_sym.
Qed.

(** Source for [symmetric_degree_orthogonal]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Homogeneous projections
    are idempotent and mutually orthogonal. *)
Lemma symmetric_degree_orthogonal m n x :
  symmetric_degree m (symmetric_degree n x) = if m == n then symmetric_degree n x else 0.
Proof. exact: grade_orthogonal. Qed.

(** Source for [symmetric_degree_finite]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Each element is the finite sum of
    its homogeneous components, including degree zero. *)
Lemma symmetric_degree_finite x : exists N, x = \sum_(i < N) symmetric_degree i x.
Proof. exact: grade_finite. Qed.

(** Source for [symmetric_unit_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The unit has degree
    zero. *)
Lemma symmetric_unit_homogeneous : homogeneous (symmetric_grading V) 0 (symmetric_unit V).
Proof. exact: (symmetric_word_homogeneous [::]). Qed.

(** Source for [symmetric_generator_homogeneous]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Every generator has
    degree one. *)
Lemma symmetric_generator_homogeneous v :
  homogeneous (symmetric_grading V) 1 (symmetric_generator v).
Proof. exact: (symmetric_word_homogeneous [:: v]). Qed.

(** Source for [symmetric_degree_projection]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Taking a homogeneous
    component commutes with the tensor projection. *)
Lemma symmetric_degree_projection n x :
  symmetric_degree n (symmetric_projection V x) = symmetric_projection V (tensor_degree n x).
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_degree_word symmetric_projection_word symmetric_degree_word.
by case: ifP => _; rewrite ?symmetric_projection_word ?linear0.
Qed.

(** Source for [symmetric_projection_graded]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The tensor projection
    preserves homogeneous degree. *)
Lemma symmetric_projection_graded :
  preserves_grading (tensor_grading V) (symmetric_grading V) (symmetric_projection V).
Proof.
move=> n x hx; rewrite /homogeneous -/(symmetric_degree n _).
by rewrite symmetric_degree_projection hx.
Qed.

(** Source for [symmetric_product_components]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The product of projected
    degree-m and degree-n elements has degree m+n. *)
Lemma symmetric_product_components m n x y :
  homogeneous (symmetric_grading V) (m + n)%N
    (symmetric_product (symmetric_degree m x) (symmetric_degree n y)).
Proof.
have b := symmetric_product_bilinear V.
elim/symmetric_word_induction: x => [|x x' hx hx'|a x hx|s].
- by rewrite linear0 (bil0l b); exact: homogeneous0.
- by rewrite linearD (bilDl b); exact: homogeneousD.
- by rewrite linearZ (bilZl b); exact: homogeneousZ.
elim/symmetric_word_induction: y => [|y y' hy hy'|a y hy|t].
- by rewrite linear0 (bil0r b); exact: homogeneous0.
- by rewrite linearD (bilDr b); exact: homogeneousD.
- by rewrite linearZ (bilZr b); exact: homogeneousZ.
rewrite !symmetric_degree_word.
case: (eqVneq (size s) m) => [<-|_]; last first.
  by rewrite (bil0l b); exact: homogeneous0.
case: (eqVneq (size t) n) => [<-|_]; last first.
  by rewrite (bil0r b); exact: homogeneous0.
by rewrite symmetric_word_cat -size_cat; exact: symmetric_word_homogeneous.
Qed.

(** Source for [symmetric_product_graded]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Multiplication adds homogeneous
    degrees. *)
Lemma symmetric_product_graded : graded_product (symmetric_grading V) (@symmetric_product K V).
Proof.
move=> m n x y hx hy.
by rewrite -hx -hy; exact: symmetric_product_components.
Qed.

(** Source for [graded_symmetric_algebra]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The symmetric algebra with its
    homogeneous grading and graded multiplication. *)
Definition graded_symmetric_algebra : graded_algebra K :=
  @GradedAlgebra K E (symmetric_grading V) (@symmetric_product K V) (symmetric_product_bilinear V) symmetric_product_graded.

(** Source for [symmetric_component_induction]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Words of length n span
    the degree-n component and give its induction principle. *)
Lemma symmetric_component_induction n (P : E -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, size s = n -> P (symmetric_word s)) :
    forall x, homogeneous (symmetric_grading V) n x -> P x.
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

Section SymmetricWords.
Variable Z : lmodType K.
Variable beta : seq V -> Z.
Hypothesis hb : multilinear_words beta.
Hypothesis ha : forall s t, perm_eq s t -> beta s = beta t.

(** Source for [symmetric_word_component]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Restrict a symmetric function of
    words to words of a fixed length. *)
Definition symmetric_word_component m
    (x : {dffun forall i : 'I_m, power_family V m i}) : Z := beta (power_seq x).

(** Source for [symmetric_word_component_multilinear]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The fixed-length
    restriction of a multilinear word function is multilinear. *)
Lemma symmetric_word_component_multilinear m :
  multilinear (@symmetric_word_component m).
Proof. exact: multilinear_words_power hb. Qed.

(** Source for [symmetric_word_component_symmetric]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The fixed-length
    restriction preserves symmetry under permutations. *)
Lemma symmetric_word_component_symmetric m :
  symmetric_power_function (@symmetric_word_component m).
Proof. by move=> x y hxy; exact: ha. Qed.

(** Source for [symmetric_word_sig]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Choose the unique fixed-degree
    linear extension supplied by the abstract universal property. *)
Definition symmetric_word_sig m :=
  boolp.cid (symmetric_power_universal H (@symmetric_word_component_multilinear m)
    (@symmetric_word_component_symmetric m)).

(** Source for [symmetric_word_map]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The chosen linear extension in a
    single homogeneous degree. *)
Definition symmetric_word_map m : {linear symmetric_algebra V -> Z} :=
  proj1_sig (symmetric_word_sig m).

(** Source for [symmetric_word_extension_fun]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Assemble the homogeneous
    extensions using the finite graded sum. *)
Definition symmetric_word_extension_fun : E -> Z :=
  graded_sum (symmetric_grading V) symmetric_word_map.
HB.instance Definition _ := GRing.Linear.copy symmetric_word_extension_fun
  (graded_sum (symmetric_grading V) symmetric_word_map).

(** Source for [symmetric_word_extension]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The linear extension of a symmetric
    multilinear word function to the algebra. *)
Definition symmetric_word_extension : {linear E -> Z} :=
  GRing.Linear.clone _ _ _ _ symmetric_word_extension_fun _.

(** Source for [symmetric_word_extensionE]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The linear extension
    evaluates each generator word as prescribed. *)
Lemma symmetric_word_extensionE s : symmetric_word_extension (symmetric_word s) = beta s.
Proof.
rewrite /= /symmetric_word_extension_fun.
rewrite (graded_sum_homogeneous _ (symmetric_word_homogeneous s)).
have := proj1 (proj2 (proj2_sig (symmetric_word_sig (size s)))) (seq_power s).
by rewrite /algebra_power /symmetric_word_component power_seqK.
Qed.
End SymmetricWords.

(** Source for [word_degree_one_symmetric]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The function retaining
    only one-letter words is invariant under permutations. *)
Lemma word_degree_one_symmetric (s t : seq V) :
  perm_eq s t -> word_degree_one s = word_degree_one t.
Proof.
move=> hp; case: (leqP (size t) 1) => ht.
- by rewrite (perm_small_eq ht hp).
have hs : (1 < size s)%N by rewrite (perm_size hp).
clear hp; by case: s hs => [|v [|w s]]; case: t ht => [|v' [|w' t]].
Qed.

(** Source for [symmetric_degree_one]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The degree-one evaluation into the
    original vector space. *)
Definition symmetric_degree_one : {linear E -> V} :=
  symmetric_word_extension (@word_degree_one_multilinear K V) word_degree_one_symmetric.

(** Source for [symmetric_degree_one_word]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Degree-one evaluation
    retains one-letter words and kills all other word lengths. *)
Lemma symmetric_degree_one_word s : symmetric_degree_one (symmetric_word s) = word_degree_one s.
Proof. exact: symmetric_word_extensionE. Qed.

(** Source for [symmetric_degree_one_projection]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Degree-one evaluation
    agrees before and after tensor projection. *)
Lemma symmetric_degree_one_projection x :
  symmetric_degree_one (symmetric_projection V x) = tensor_degree_one V x.
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite symmetric_projection_word symmetric_degree_one_word tensor_degree_one_word.
Qed.

(** Source for [symmetric_generatorK]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Degree-one evaluation is a left
    inverse of the generator inclusion. *)
Lemma symmetric_generatorK : cancel (@symmetric_generator K V) symmetric_degree_one.
Proof. by move=> v; rewrite /symmetric_generator symmetric_degree_one_word. Qed.

(** Source for [symmetric_generator_injective]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The generator inclusion
    is injective. *)
Lemma symmetric_generator_injective : injective (@symmetric_generator K V).
Proof. exact: can_inj symmetric_generatorK. Qed.

(** Source for [symmetric_degree_one_reconstruction]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Projecting onto degree
    one is inclusion composed with degree-one evaluation. *)
Lemma symmetric_degree_one_reconstruction x :
  symmetric_degree 1 x = symmetric_generator (symmetric_degree_one x).
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite symmetric_degree_word symmetric_degree_one_word.
by case: s => [|v [|w s]] /=; rewrite /word_degree_one /= ?linear0.
Qed.

(** Source for [symmetric_first_component]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Every degree-one element
    comes from its degree-one evaluation in V. *)
Lemma symmetric_first_component x : homogeneous (symmetric_grading V) 1 x ->
  symmetric_generator (symmetric_degree_one x) = x.
Proof. by move=> hx; rewrite -symmetric_degree_one_reconstruction; exact: hx. Qed.

(** Source for [word_degree_zero_symmetric]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: The function retaining
    only the empty word is invariant under permutations. *)
Lemma word_degree_zero_symmetric (s t : seq V) :
  perm_eq s t -> word_degree_zero s = word_degree_zero t.
Proof.
move=> hp; case: (leqP (size t) 1) => ht.
- by rewrite (perm_small_eq ht hp).
have hs : (1 < size s)%N by rewrite (perm_size hp).
clear hp; by case: s hs => [|v [|w s]]; case: t ht => [|v' [|w' t]].
Qed.

(** Source for [symmetric_augmentation]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The scalar-valued degree-zero
    evaluation. *)
Definition symmetric_augmentation : {linear E -> K^o} :=
  symmetric_word_extension (@word_degree_zero_multilinear K V) word_degree_zero_symmetric.

(** Source for [symmetric_augmentation_word]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Augmentation sends the
    empty word to one and nonempty words to zero. *)
Lemma symmetric_augmentation_word s :
  symmetric_augmentation (symmetric_word s) = word_degree_zero s.
Proof. exact: symmetric_word_extensionE. Qed.

(** Source for [symmetric_augmentation_projection]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Augmentation agrees
    before and after tensor projection. *)
Lemma symmetric_augmentation_projection x :
  symmetric_augmentation (symmetric_projection V x) = tensor_augmentation V x.
Proof.
elim/tensor_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite symmetric_projection_word symmetric_augmentation_word tensor_augmentation_word.
Qed.

(** Source for [symmetric_augmentation_unit]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Augmentation sends the
    unit to scalar one. *)
Lemma symmetric_augmentation_unit : symmetric_augmentation (symmetric_unit V) = 1.
Proof. exact: (symmetric_augmentation_word [::]). Qed.

(** Source for [symmetric_scalar]: Federer 1.9.1, p. 41, homogeneous powers,
    spanning and low-degree identifications. Supporting definition or lemma
    for this passage, in words: Scalar inclusion by multiplication of the
    algebra unit. *)
Definition symmetric_scalar (a : K^o) : E := (a : K) *: symmetric_unit V.

(** Source for [symmetric_scalar_linear]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Scalar inclusion is linear. *)
Lemma symmetric_scalar_linear : linear symmetric_scalar.
Proof. by move=> a b c; rewrite /symmetric_scalar scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o E
  *:%R symmetric_scalar symmetric_scalar_linear.

(** Source for [symmetric_scalarK]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: Augmentation is a left inverse of
    scalar inclusion. *)
Lemma symmetric_scalarK : cancel symmetric_scalar symmetric_augmentation.
Proof.
move=> a; rewrite /symmetric_scalar linearZ symmetric_augmentation_unit.
change ((a : K) * 1 = a); exact: mulr1.
Qed.

(** Source for [symmetric_scalar_injective]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Scalar inclusion is
    injective. *)
Lemma symmetric_scalar_injective : injective symmetric_scalar.
Proof. exact: can_inj symmetric_scalarK. Qed.

(** Source for [symmetric_degree_zero_reconstruction]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Degree-zero projection
    is scalar inclusion composed with augmentation. *)
Lemma symmetric_degree_zero_reconstruction x :
  symmetric_degree 0 x = symmetric_scalar (symmetric_augmentation x).
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite symmetric_degree_word symmetric_augmentation_word /symmetric_scalar.
by case: s => [|v s] /=; rewrite /word_degree_zero /= ?scale1r ?scale0r.
Qed.

(** Source for [symmetric_zeroth_component]: Federer 1.9.1, p. 41,
    homogeneous powers, spanning and low-degree identifications. Supporting
    definition or lemma for this passage, in words: Every degree-zero
    element is the scalar inclusion of its augmentation. *)
Lemma symmetric_zeroth_component x : homogeneous (symmetric_grading V) 0 x ->
  symmetric_scalar (symmetric_augmentation x) = x.
Proof. by move=> hx; rewrite -symmetric_degree_zero_reconstruction; exact: hx. Qed.

(** Source for [symmetric_unit_nonzero]: Federer 1.9.1, p. 41, homogeneous
    powers, spanning and low-degree identifications. Supporting definition
    or lemma for this passage, in words: The algebra unit is nonzero because
    its augmentation is one. *)
Lemma symmetric_unit_nonzero : symmetric_unit V != 0.
Proof.
apply/eqP=> h; have e := symmetric_augmentation_unit.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End SymmetricGrading.
Arguments symmetric_degree {K V} n.
